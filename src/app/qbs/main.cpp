/****************************************************************************
**
** Copyright (C) 2012 Digia Plc and/or its subsidiary(-ies).
** Contact: http://www.qt-project.org/legal
**
** This file is part of the Qt Build Suite.
**
** Commercial License Usage
** Licensees holding valid commercial Qt licenses may use this file in
** accordance with the commercial license agreement provided with the
** Software or, alternatively, in accordance with the terms contained in
** a written agreement between you and Digia.  For licensing terms and
** conditions see http://qt.digia.com/licensing.  For further information
** use the contact form at http://qt.digia.com/contact-us.
**
** GNU Lesser General Public License Usage
** Alternatively, this file may be used under the terms of the GNU Lesser
** General Public License version 2.1 as published by the Free Software
** Foundation and appearing in the file LICENSE.LGPL included in the
** packaging of this file.  Please review the following information to
** ensure the GNU Lesser General Public License version 2.1 requirements
** will be met: http://www.gnu.org/licenses/old-licenses/lgpl-2.1.html.
**
** In addition, as a special exception, Digia gives you certain additional
** rights.  These rights are described in the Digia Qt LGPL Exception
** version 1.1, included in the file LGPL_EXCEPTION.txt in this package.
**
****************************************************************************/

#include "application.h"
#include "consoleprogressobserver.h"
#include "showproperties.h"
#include "status.h"

#include <app/shared/commandlineparser.h>
#include <buildgraph/buildgraph.h>
#include <buildgraph/executor.h>
#include <language/sourceproject.h>
#include <logging/consolelogger.h>
#include <logging/logger.h>
#include <tools/hostosinfo.h>
#include <tools/runenvironment.h>

#include <QCoreApplication>
#include <QDir>
#include <QObject>
#include <QProcess>
#include <QProcessEnvironment>
#include <QScopedPointer>
#include <QTimer>

using namespace qbs;

enum ExitCode
{
    ExitCodeOK = 0,
    ExitCodeErrorParsingCommandLine = 1,
    ExitCodeErrorCommandNotImplemented = 2,
    ExitCodeErrorExecutionFailed = 3,
    ExitCodeErrorLoadingProjectFailed = 4,
    ExitCodeErrorBuildFailure = 5
};

static QList<ResolvedProduct::ConstPtr> productsToUse(const QList<ResolvedProject::ConstPtr> &projects,
                                                        const QStringList &selectedProducts)
{
    QList<ResolvedProduct::ConstPtr> products;
    QStringList productNames;
    const bool useAll = selectedProducts.isEmpty();
    foreach (const ResolvedProject::ConstPtr &project, projects) {
        foreach (const ResolvedProduct::ConstPtr &product, project->products) {
            if (useAll || selectedProducts.contains(product->name)) {
                products << product;
                productNames << product->name;
            }
        }
    }

    foreach (const QString &productName, selectedProducts) {
        if (!productNames.contains(productName)) {
            qbsWarning() << QCoreApplication::translate("qbs", "No such product '%1'.")
                            .arg(productName);
        }
    }

    return products;
}

static bool tryToRunTool(const QStringList &arguments, int &exitCode)
{
    if (arguments.isEmpty())
        return false;
    qputenv("PATH", QCoreApplication::applicationDirPath().toLocal8Bit()
            + HostOsInfo::pathListSeparator().toLatin1() + QByteArray(qgetenv("PATH")));
    QStringList subProcessArgs = arguments;
    const QString subProcess = subProcessArgs.takeFirst();
    if (subProcess.startsWith(QLatin1Char('-')))
        return false;
    exitCode = QProcess::execute(QLatin1String("qbs-") + subProcess, subProcessArgs);
    return exitCode != -2;
}

static int makeClean()
{
    // ### TODO: take selected products into account!
    QString errorMessage;
    const QString buildPath = FileInfo::resolvePath(QDir::currentPath(),
            QLatin1String("build"));
    if (!removeDirectoryWithContents(buildPath, &errorMessage)) {
        qbsError() << errorMessage;
        return ExitCodeErrorExecutionFailed;
    }
    return 0;
}

static int runShell(SourceProject &sourceProject, const ResolvedProject::ConstPtr &project)
{
    try {
        RunEnvironment runEnvironment = sourceProject.getRunEnvironment(project->products.first(),
                QProcessEnvironment::systemEnvironment());
        return runEnvironment.runShell();
    } catch (const Error &error) {
        qbsError() << error.toString();
        return EXIT_FAILURE;
    }
}

class AbstractBuilder : public QObject
{
    Q_OBJECT

protected:
    AbstractBuilder(SourceProject &sourceProject, const BuildOptions &buildOptions)
        : m_sourceProject(sourceProject), m_buildOptions(buildOptions)
    {
    }

    SourceProject &sourceProject() const { return m_sourceProject; }
    const BuildOptions buildOptions() const { return m_buildOptions; }

private slots:
    void build()
    {
        try {
            doBuild();
            qApp->quit();
        } catch (const Error &error) {
            qbsError() << error.toString();
            qApp->exit(ExitCodeErrorBuildFailure);
        }
    }

private:
    virtual void doBuild() = 0;

    SourceProject &m_sourceProject;
    const BuildOptions m_buildOptions;
};

class ProductsBuilder : public AbstractBuilder
{
public:
    ProductsBuilder(SourceProject &sourceProject, const QList<ResolvedProduct::ConstPtr> &products,
                    const BuildOptions &buildOptions)
        : AbstractBuilder(sourceProject, buildOptions), m_products(products)
    {
    }

private:
    void doBuild() { sourceProject().buildProducts(m_products, buildOptions()); }

    const QList<ResolvedProduct::ConstPtr> m_products;
};

class ProjectsBuilder : public AbstractBuilder
{
public:
    ProjectsBuilder(SourceProject &sourceProject, const QList<ResolvedProject::ConstPtr> &projects,
                    const BuildOptions &buildOptions)
        : AbstractBuilder(sourceProject, buildOptions), m_projects(projects)
    {
    }

private:
    void doBuild() { sourceProject().buildProjects(m_projects, buildOptions()); }

    const QList<ResolvedProject::ConstPtr> m_projects;
};

static int build(SourceProject &sourceProject, const QList<ResolvedProject::ConstPtr> &projects,
                 const QStringList &productsSetByUser, const BuildOptions &buildOptions)
{
    QScopedPointer<AbstractBuilder> builder;
    if (productsSetByUser.isEmpty()) {
        builder.reset(new ProjectsBuilder(sourceProject, projects, buildOptions));
    } else {
        const QList<ResolvedProduct::ConstPtr> products
                = productsToUse(projects, productsSetByUser);
        builder.reset(new ProductsBuilder(sourceProject, products, buildOptions));
    }
    QTimer::singleShot(0, builder.data(), SLOT(build()));
    return qApp->exec();
}

static int runTarget(SourceProject &sourceProject, const QList<ResolvedProduct::ConstPtr> &products,
                     const QString &targetName, const QStringList &arguments)
{
    try {
        ResolvedProduct::ConstPtr productToRun;
        QString productFileName;

        foreach (const ResolvedProduct::ConstPtr &product, products) {
            const QString executable = sourceProject.targetExecutable(product);
            if (executable.isEmpty())
                continue;
            if (!targetName.isEmpty() && !executable.endsWith(targetName))
                continue;
            if (!productFileName.isEmpty()) {
                qbsError() << QObject::tr("There is more than one executable target in "
                                          "the project. Please specify which target "
                                          "you want to run.");
                return EXIT_FAILURE;
            }
            productFileName = executable;
            productToRun = product;
        }

        if (!productToRun) {
            if (targetName.isEmpty())
                qbsError() << QObject::tr("Can't find a suitable product to run.");
            else
                qbsError() << QObject::tr("No such target: '%1'").arg(targetName);
            return ExitCodeErrorBuildFailure;
        }

        RunEnvironment runEnvironment = sourceProject.getRunEnvironment(productToRun,
                                                                        QProcessEnvironment::systemEnvironment());
        return runEnvironment.runTarget(productFileName, arguments);
    } catch (const Error &error) {
        qbsError() << error.toString();
        return EXIT_FAILURE;
    }
}

int main(int argc, char *argv[])
{
    ConsoleLogger cl;

    Application app(argc, argv);
    app.init();
    QStringList arguments = app.arguments();
    arguments.removeFirst();

    int toolExitCode;
    if (tryToRunTool(arguments, toolExitCode))
        return toolExitCode;

    CommandLineParser parser;
    if (!parser.parseCommandLine(arguments)) {
        parser.printHelp();
        return ExitCodeErrorParsingCommandLine;
    }

    if (parser.isHelpSet()) {
        parser.printHelp();
        return 0;
    }

    QList<ResolvedProject::ConstPtr> resolvedProjects;
    SourceProject sourceProject;
    sourceProject.setBuildRoot(QDir::currentPath());
    QScopedPointer<ConsoleProgressObserver> observer;
    if (parser.showProgress()) {
        observer.reset(new ConsoleProgressObserver);
        sourceProject.setProgressObserver(observer.data());
    }
    try {
        foreach (const QVariantMap &buildConfig, parser.buildConfigurations()) {
            const ResolvedProject::ConstPtr resolvedProject
                    = sourceProject.setupResolvedProject(parser.projectFileName(), buildConfig);
            resolvedProjects << resolvedProject;
        }
    } catch (const Error &error) {
        qbsError() << error.toString();
        return ExitCodeErrorLoadingProjectFailed;
    }

    switch (parser.command()) {
    case CommandLineParser::CleanCommand:
        return makeClean();
    case CommandLineParser::StartShellCommand:
        return runShell(sourceProject, resolvedProjects.first());
    case CommandLineParser::StatusCommand:
        return printStatus(parser.projectFileName(), resolvedProjects);
    case CommandLineParser::PropertiesCommand:
        return showProperties(productsToUse(resolvedProjects, parser.products()));
    case CommandLineParser::BuildCommand:
        return build(sourceProject, resolvedProjects, parser.products(), parser.buildOptions());
    case CommandLineParser::RunCommand: {
        const int buildExitCode = build(sourceProject, resolvedProjects, parser.products(),
                                        parser.buildOptions());
        if (buildExitCode != 0)
            return buildExitCode;
        const QList<ResolvedProduct::ConstPtr> products
                = productsToUse(resolvedProjects, parser.products());
        return runTarget(sourceProject, products, parser.runTargetName(), parser.runArgs());
    }
    }
}

#include "main.moc"

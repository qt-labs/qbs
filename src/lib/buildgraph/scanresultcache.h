/**************************************************************************
**
** This file is part of the Qt Build Suite
**
** Copyright (c) 2012 Nokia Corporation and/or its subsidiary(-ies).
**
** Contact: Nokia Corporation (info@qt.nokia.com)
**
**
** GNU Lesser General Public License Usage
**
** This file may be used under the terms of the GNU Lesser General Public
** License version 2.1 as published by the Free Software Foundation and
** appearing in the file LICENSE.LGPL included in the packaging of this file.
** Please review the following information to ensure the GNU Lesser General
** Public License version 2.1 requirements will be met:
** http://www.gnu.org/licenses/old-licenses/lgpl-2.1.html.
**
** In addition, as a special exception, Nokia gives you certain additional
** rights. These rights are described in the Nokia Qt LGPL Exception
** version 1.1, included in the file LGPL_EXCEPTION.txt in this package.
**
** GNU General Public License Usage
** Alternatively, this file may be used under the terms of the GNU General
** Public License version 3.0 as published by the Free Software Foundation
** and appearing in the file LICENSE.GPL included in the packaging of this
** file.
** Please review the following information to ensure the GNU General
** Public License version 3.0 requirements will be met:
** http://www.gnu.org/copyleft/gpl.html.
**
** Other Usage
** Alternatively, this file may be used in accordance with the terms and
** conditions contained in a signed written agreement between you and Nokia.
**
**************************************************************************/
#ifndef SCANRESULTCACHE_H
#define SCANRESULTCACHE_H

#include <QtCore/QHash>
#include <QtCore/QMutex>
#include <QtCore/QSet>
#include <QtCore/QString>
#include <QtCore/QVector>

namespace qbs {

class ScanResultCache
{
public:
    class Dependency
    {
    public:
        Dependency() : m_isLocal(false), m_isClean(true) {}
        Dependency(const QString &filePath, bool m_isLocal);

        QString filePath() const { return m_dirPath.isEmpty() ? m_fileName : m_dirPath + QLatin1Char('/') + m_fileName; }
        const QString &dirPath() const { return m_dirPath; }
        const QString &fileName() const { return m_fileName; }
        bool isLocal() const { return m_isLocal; }
        bool isClean() const { return m_isClean; }

    private:
        QString m_dirPath;
        QString m_fileName;
        bool m_isLocal;
        bool m_isClean;
    };

    struct Result
    {
        Result()
            : valid(false)
        {}

        QVector<Dependency> deps;
        bool valid;
    };

    Result value(const QString &fileName) const;
    void insert(const QString &fileName, const Result &value);

private:
    mutable QMutex m_mutex;
    QHash<QString, Result> m_data;
};

} // namespace qbs

#endif // SCANRESULTCACHE_H

import re

def parseLoadPath():
    d = dict()
    with open('PrintLoadPath.txt') as f:
        for line in f:
            a = line.strip().split()
            if len(a) == 2:
                d[a[0]] = a[1]
    return d

loadPath = parseLoadPath()

def getLibraryList():
    global loadPath
    l = []
    with open('PrintLibraries.txt') as f:
        for line in f:
            m = re.match(r'  (.*)\.([^.]+)', line.rstrip())
            if m:
                logicalDir = m[1]
                libName = m[2]
                physicalDir = loadPath[logicalDir]
                l.append(f'{physicalDir}/{libName}.v')
            else:
                assert(line == "Loaded library files:\n")
    return l

def getRoots():
    global loadPath
    s = set()
    for logicalDir in loadPath:
        m = re.match(r'([^.]+)', logicalDir)
        root = m[1]
        if root != '<>':
            s.add(m[1])
    return s

print('\n'.join(getLibraryList()))
print(getRoots())

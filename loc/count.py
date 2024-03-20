# Usage:
#
# At the end of src/Bedrock/End2End/X25519/GarageDoorTop.v, insert the following commands:
#
# Set Printing Width 10000.
# Print LoadPath.
# Print Libraries.
#
# and copy-paste their outputs to loc/PrintLoadPath.txt and loc/PrintLibraries.txt, respectively.
# Append '  Crypto.Bedrock.End2End.X25519.GarageDoorTop' to loc/PrintLibraries.txt.
# Then, run
# python3 loc/count.py

import re
import collections
import subprocess
from subprocess import PIPE

def parseLoadPath():
    d = dict()
    with open('./loc/PrintLoadPath.txt') as f:
        for line in f:
            a = line.strip().split()
            if len(a) == 2:
                d[a[0]] = a[1]
    return d

loadPath = parseLoadPath()

def rootOfLogicalDir(logicalDir, maxDepth = 1):
    a = logicalDir.split('.')
    root = a[0]
    # we treat the toplevel Ltac2 root as if it was under Coq
    if root == 'Ltac2':
        return 'Coq'
    elif root == 'Crypto' and len(a) > 1 and maxDepth > 1:
        if a[1] == 'Bedrock' and len(a) > 2 and maxDepth > 2:
            if a[2] == 'Field' and len(a) > 3 and maxDepth > 3:
                return a[0] + '.' + a[1] + '.' + a[2] + '.' + a[3]
            else:
                return a[0] + '.' + a[1] + '.' + a[2]
        else:
            return a[0] + '.' + a[1]
    else:
        return root

def rootToSortKey(originalroot):
    root = originalroot.lower()
    if root == 'coq':
        return 'a'
    if root.startswith('crypto'):
        return root[2:]
    return root

def logicalPath_to_absolutePhysical(logicalPath):
    global loadPath
    m = re.match(r'(.*)\.([^.]+)', logicalPath)
    logicalDir = m[1]
    libName = m[2]
    physicalDir = loadPath[logicalDir]
    return f'{physicalDir}/{libName}.v'

def logicalDir_of_logicalPath(logicalPath):
    m = re.match(r'(.*)\.([^.]+)', logicalPath)
    return m[1]

# returns a dictionary that maps logical roots (eg Coq, bedrock2, riscv, Crypto, ...)
# to lists of absolute paths
def getLibraries():
    libs = collections.defaultdict(list)
    with open('./loc/PrintLibraries.txt') as f:
        for line in f:
            if line.startswith('  '):
                absPath = logicalPath_to_absolutePhysical(line.strip())
                root = rootOfLogicalDir(logicalDir_of_logicalPath(line.strip()))
                libs[root].append(absPath)
            elif line == "Loaded library files:\n":
                pass
            else:
                print('Warning: unexpected line:')
                print(line)
    return libs

def printLibraries():
    for root, files in getLibraries().items():
        print(f'{root}:')
        for file in files:
            print(f'  {file}')

def parse_cloc_output(stdout_data):
    #sample output:
    #
    #files,language,blank,comment,code,"github.com/AlDanial/cloc v 1.90"
    #599,Coq,16445,8171,132933
    #599,SUM,16445,8171,132933
    a = stdout_data.split(',')
    return int(a[-1]) # last number is the one we want

def cloc_list_of_coq_files(filePaths, name):
    listPath = './loc/FileLists/' + name + '.txt'
    with open(listPath, 'w') as f:
        for line in filePaths:
            f.write(f"{line}\n")
    p = subprocess.Popen(['cloc', '--list-file=' + listPath, '--include-lang=Coq',
                          '--csv', '--quiet', '--hide-rate'],
                         stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True)
    (stdout_data, stderr_data) = p.communicate()
    if stderr_data:
        print(stderr_data)
    return parse_cloc_output(stdout_data)

def cloc_one_coq_file(coqFilePath):
    p = subprocess.Popen(['cloc', '--csv', '--quiet', '--hide-rate', coqFilePath],
                         stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True)
    (stdout_data, stderr_data) = p.communicate()
    if stderr_data:
        print(stderr_data)
    return parse_cloc_output(stdout_data)

libs = getLibraries()

def count_all_used_code():
    global libs
    totalLoc = 0
    for root in sorted(libs.keys(), key=rootToSortKey):
        c = cloc_list_of_coq_files(libs[root], root)
        totalLoc += c
        print(f'{root:40s} & {c:6d} \\\\')
    print('\\hline')
    print(f'{"Total":40s} & {totalLoc:6d} \\\\')

def count_new_code():
    global libs
    with open('./loc/new_work.txt') as f:
        totalLoc = 0
        currentTopic = None
        locOfCurrentTopic = 0
        def endCurrentTopic():
            nonlocal locOfCurrentTopic, currentTopic, totalLoc
            m = re.match(r'(.*) \((.*)\) \[(.*)\]', currentTopic)
            descr = m[1]
            fnames = m[2]
            technique = m[3]
            print(f'{descr:35s} & {technique:17s} & {locOfCurrentTopic:6d} \\\\')
            totalLoc += locOfCurrentTopic
            locOfCurrentTopic = 0
        for line0 in f:
            line = line0.strip()
            if line.startswith('#') and len(line) > 3:
                if currentTopic:
                    endCurrentTopic()
                currentTopic = line[3:]
            elif line:
                a = line.split(' ')
                if len(a) > 1:
                    locOfCurrentTopic += int(a[0])
                else:
                    p = logicalPath_to_absolutePhysical(line)
                    locOfCurrentTopic += cloc_one_coq_file(p)
        endCurrentTopic()
        print('\\hline')
        print(f'{"Total":35s} & {"":17s} & {totalLoc:6d} \\\\')

count_new_code()
print("")
count_all_used_code()

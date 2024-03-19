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

def rootOfLogicalDir(logicalDir):
    a = logicalDir.split('.')
    root = a[0]
    # we treat the toplevel Ltac2 root as if it was under Coq
    if root == 'Ltac2':
        return 'Coq'
    elif root == 'Crypto' and len(a) > 1:
        if a[1] == 'Bedrock' and len(a) > 2:
            if a[2] == 'Field' and len(a) > 3:
                return a[0] + '.' + a[1] + '.' + a[2] + '.' + a[3]
            else:
                return a[0] + '.' + a[1] + '.' + a[2]
        else:
            return a[0] + '.' + a[1]
    else:
        return root

def rootToSortKey(root):
    if root == 'Coq':
        return 'A'
    if root.startswith('Crypto'):
        return root[2:]
    return root

# returns a dictionary that maps logical roots (eg Coq, bedrock2, riscv, Crypto, ...)
# to lists of absolute paths
def getLibraries():
    global loadPath
    libs = collections.defaultdict(list)
    with open('./loc/PrintLibraries.txt') as f:
        for line in f:
            m = re.match(r'  (.*)\.([^.]+)', line.rstrip())
            if m:
                logicalDir = m[1]
                libName = m[2]
                physicalDir = loadPath[logicalDir]
                root = rootOfLogicalDir(logicalDir)
                absPath = f'{physicalDir}/{libName}.v'
                libs[root].append(absPath)
            else:
                assert(line == "Loaded library files:\n")
    return libs

def printLibraries():
    for root, files in getLibraries().items():
        print(f'{root}:')
        for file in files:
            print(f'  {file}')

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
    #sample output:
    #
    #files,language,blank,comment,code,"github.com/AlDanial/cloc v 1.90"
    #599,Coq,16445,8171,132933
    #599,SUM,16445,8171,132933
    a = stdout_data.split(',')
    return int(a[-1]) # last number is the one we want

def go():
    libs = getLibraries()
    for root in sorted(libs.keys(), key=rootToSortKey):
        c = cloc_list_of_coq_files(libs[root], root)
        print(f'{root}: {c}')

go()

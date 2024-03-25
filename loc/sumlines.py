import re
#import tempfile
import os

#import count
import collections
import subprocess
from subprocess import PIPE

#copied
def cloc_one_coq_file(coqFilePath):
    p = subprocess.Popen(['cloc', '--csv', '--quiet', '--hide-rate', coqFilePath],
                         stdout=PIPE, stdin=PIPE, stderr=PIPE, text=True)
    (stdout_data, stderr_data) = p.communicate()
    if stderr_data:
        print(stderr_data)
    return parse_cloc_output(stdout_data)
    
    
def parse_cloc_output(stdout_data):
    #sample output:
    #
    #files,language,blank,comment,code,"github.com/AlDanial/cloc v 1.90"
    #599,Coq,16445,8171,132933
    #599,SUM,16445,8171,132933
    a = stdout_data.split(',')
    return int(a[-1]) # last number is the one we want
    
def __main__():
    start = False
    name = None
    currentFile = None
    output = {}
    lastCategory = None
    lastLine = None

    def clocViaTemp(start, stop):
        nonlocal currentFile
        tempname = "./TMPFILEDONOTSAVE.v"
        # want tempfile.NamedTemporaryFile(mode="w+") 
        # but it doesn't work across processes
        try: os.remove(tempname)
        except: pass
        with open(tempname, "a+") as temp:
            with open(currentFile) as curr:
                for i, line in enumerate(curr):
                    # account for 1-indexing
                    idx = i + 1
                    if start <= idx and idx < stop:
                        temp.write(line)
        loc = cloc_one_coq_file(tempname)
        #with open(tempname) as t:
        #    print("==========================================")
        #    input(t.read())
        os.remove(tempname)
        return loc
        

    def incrementCount(category, start, stop):
        nonlocal output, name
        loc = clocViaTemp(start, stop)
        #difference = stop - start
        if category in output[name]:
            output[name][category] = output[name][category] + loc
        else:
            output[name][category] = loc

    def processLine(line):
        nonlocal name, output, lastCategory, lastLine, currentFile
        #check for header
        headerMatch = re.match("#(.+)", line)
        fileMatch = re.match("!(.+)", line)
        if headerMatch:
            name = headerMatch.group(1)
            output[name] = {}
        elif fileMatch:
            lastLine = None
            lastCategory = None
            currentFile = fileMatch.group(1)
            print(currentFile)
        else:
            obj = re.match("(\d+): (.*)", line)
            line = int(obj.group(1))
            category = obj.group(2)
            if lastLine:
                incrementCount(lastCategory, lastLine, line)
            lastLine = line
            lastCategory = category

    with open('./loc/ChaCha & Montgomery LOC methods.txt') as fp:
        for line in fp:
            if re.match("===+", line): start = True
            elif re.match("\n", line): continue
            elif start: processLine(line)
    print(output)
    print("ChaCha line count ", sum(output["ChaCha"].values()))
    print("Montgomery line count ", sum(output["Montgomery"].values()))
    
__main__()

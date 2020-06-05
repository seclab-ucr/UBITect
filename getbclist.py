import sys
import os.path
import os
cur_dir=os.getcwd()

def renameBB(argv):
    llvm_dir = argv[1]
    for dirpath, dirnames, filenames in os.walk(cur_dir):
        for filename in filenames:
            if os.path.splitext(filename)[1] == ".llbc":
	        newfile = os.path.splitext(filename)[0] +".bc"
	        current = os.path.join(dirpath, filename)
                module = os.path.join(dirpath, newfile)
	        cmd = llvm_dir + "/build/bin/opt -load " + llvm_dir + "/build/lib/bbTaglib.so -bbtag "+ current+" >>"+ module
                os.system(cmd)
def getBC():
    file_abs = cur_dir + "/bitcode.list"
    for dirpath, dirnames, filenames in os.walk(cur_dir):
        for filename in filenames:
            if os.path.splitext(filename)[1] == ".bc":
                module = os.path.join(dirpath, filename)
                if "timeconst.bc" in module:
                    continue
                with open(file_abs, "a") as f:
                    f.write(module)
                    f.write("\n")
if __name__ == "__main__":
    renameBB(sys.argv)
    getBC()

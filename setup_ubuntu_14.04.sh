rm -rf temp/
mkdir -p temp
mkdir -p z3
cd temp
curl -L -o z3.zip https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-14.04.zip
unzip z3.zip
cp z3-4.8.4.d6df51951f4c-x64-ubuntu-14.04/bin/com.microsoft.z3.jar ../z3/
cp z3-4.8.4.d6df51951f4c-x64-ubuntu-14.04/bin/libz3java.so ../z3/
cd -
rm -r temp/
echo DONE

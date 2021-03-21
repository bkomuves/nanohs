#!/bin/bash

rm nanohs_via_ghc.exe     2>/dev/null
rm nanohs_via_ghc_00.exe  2>/dev/null
rm nanohs_via_ghc_01.exe  2>/dev/null
rm nanohs_stage1.c        2>/dev/null
rm nanohs_stage2.c        2>/dev/null
rm nanohs_stage3.c        2>/dev/null
rm nanohs_stage1.exe      2>/dev/null  
rm nanohs_stage2.exe      2>/dev/null  

echo "" ; echo "==================="
echo "compiling a bootstrap (stage #0) compiler via GHC"
ghc -O0 --make -main-is Nano.main Nano.hs -o nanohs_via_ghc_O0.exe
ghc -O1 --make -main-is Nano.main Nano.hs -o nanohs_via_ghc_O1.exe

echo "" ; echo "==================="
echo "compiling a stage #1 (unoptimized) compiler via the bootstrapped one (stage #0)"
./nanohs_via_ghc_O1.exe -c Nano.hs nanohs_stage1.c 
echo "running gcc on stage #1 C source..."
gcc -O3 -Wl,-stack_size -Wl,0x4000000 nanohs_stage1.c -o nanohs_stage1.exe

echo "" ; echo "==================="
echo "compiling a stage #2 (optimized) compiler via stage #1"
./nanohs_stage1.exe -o Nano.hs nanohs_stage2.c 
echo "running gcc on stage #2 C source..."
gcc -O3 -Wl,-stack_size -Wl,0x4000000 nanohs_stage2.c -o nanohs_stage2.exe

echo "" ; echo "==================="
echo "compiling a stage #3 (optimized) compiler via stage #2"
./nanohs_stage2.exe -o Nano.hs nanohs_stage3.c 
 
echo "" ; echo "==================="
echo "comparing the stage #2 and stage #3 outputs:"
DIFF=`diff -q nanohs_stage2.c nanohs_stage3.c`
if [[ ! -z "$DIFF" ]]
then
  echo $DIFF
else
  echo OK.
fi

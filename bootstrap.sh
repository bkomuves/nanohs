#!/bin/bash

rm nanohs_via_ghc.exe  2>/dev/null
rm nanohs_via_c.exe    2>/dev/null 
rm nanohs_stage1.c     2>/dev/null
rm nanohs_stage1.exe   2>/dev/null  
rm nanohs_stage2.c     2>/dev/null
rm nanohs_stage2.exe   2>/dev/null  

echo "" ; echo "==================="
echo "compiling a bootstrap (stage #0) compiler via GHC"
ghc -O0 --make -main-is Nano.main Nano.hs -o nanohs_via_ghc.exe

echo "" ; echo "==================="
echo "compiling a stage #1 compiler via the bootstrapped one (stage #0)"
./nanohs_via_ghc.exe -c Nano.hs nanohs_stage1.c 
gcc -O -Wl,-stack_size -Wl,0x1000000 nanohs_stage1.c -o nanohs_stage1.exe

echo "" ; echo "==================="
echo "compiling a stage #2 compiler via stage #1"
./nanohs_stage1.exe -c Nano.hs nanohs_stage2.c 

# echo "" ; echo "==================="
# echo "comparing the stage #1 and stage #2 outputs:"
# diff nanohs_stage1.c nanohs_stage2.c

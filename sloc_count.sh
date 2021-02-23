#!/bin/bash

SRC="NanoHaskell.hs"

FULL=`cat              $SRC | wc -l | sed -E 's/[ ]*([1-9]+)/\1/g'` 
ANNT=`grep "::"        $SRC | wc -l | sed -E 's/[ ]*([1-9]+)/\1/g'`
TYPE=`grep "^type "    $SRC | wc -l | sed -E 's/[ ]*([1-9]+)/\1/g'`
DATA=`grep "^data "    $SRC | wc -l | sed -E 's/[ ]*([1-9]+)/\1/g'`
DCON=`grep "^  |"      $SRC | wc -l | sed -E 's/[ ]*([1-9]+)/\1/g'`
# ASML=`grep "^  , \""   $SRC | wc -l | sed -E 's/[ ]*([1-9]+)/\1/g'`

HASKELL_CLOC=`cloc --quiet --csv NanoHaskell.hs | grep Haskell`
ASM_CLOC=`cloc --quiet --csv rts.asm sys_macos.asm | grep Assembly`
C_CLOC=`cloc --quiet --csv rts.c | grep C`

IFS=',' #setting comma as delimiter  
read -a arr <<< "$HASKELL_CLOC" 
BLNK=${arr[2]}
CMMT=${arr[3]}
HSLN=${arr[4]}

read -a arr <<< "$ASM_CLOC" 
ASML=${arr[4]}

read -a arr <<< "$C_CLOC" 
CRTS=${arr[4]}

echo "raw lines         = $FULL"
echo "blank             = $BLNK"
echo "comment           = $CMMT"
echo "haskell lines     = $HSLN"
echo "type annotations  = $ANNT"
echo "type aliases      = $TYPE"
echo "data declarations = $DATA"
echo "data constructors = $DCON"

IGNORED=`expr $ANNT + $TYPE + $DATA + $DCON`
ESSENTIAL=`expr $HSLN - $IGNORED`

echo "============================"
echo "haskell lines     = $HSLN"
echo "from this ignored = $IGNORED"
echo "essential lines   = $ESSENTIAL"
echo "C runtime         = $CRTS"
echo "assembly runtime  = $ASML"

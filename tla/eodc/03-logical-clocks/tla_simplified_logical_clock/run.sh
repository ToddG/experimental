#! /bin/bash

echo "===================================================="
echo " logical_clock 1"
echo "===================================================="

echo "----------------------------------------------------"
echo "Solution 1A : One process"
echo "----------------------------------------------------"
tlc -dump dot 1A.dot -config A.cfg logical_clock1.tla && dot -Tpng 1A.dot -o 1A.png

echo "----------------------------------------------------"
echo "Solution 1B : Two processes"
echo "----------------------------------------------------"
tlc -dump dot 1B.dot -config B.cfg logical_clock1.tla && dot -Tpng 1B.dot -o 1B.png

echo "----------------------------------------------------"
echo "Solution 1C : Three processes"
echo "----------------------------------------------------"
tlc -dump dot 1C.dot -config C.cfg logical_clock1.tla && dot -Tpng 1C.dot -o 1C.png


echo "===================================================="
echo " logical_clock 2"
echo "===================================================="

echo "----------------------------------------------------"
echo "Solution 2A : One process, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 2A.dot -config A.cfg logical_clock2.tla && dot -Tpng 2A.dot -o 2A.png

echo "----------------------------------------------------"
echo "Solution 2B : Two processes, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 2B.dot -config B.cfg logical_clock2.tla && dot -Tpng 2B.dot -o 2B.png

echo "----------------------------------------------------"
echo "Solution 2C : Three processes, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 2C.dot -config C.cfg logical_clock2.tla && dot -Tpng 2C.dot -o 2C.png


echo "===================================================="
echo " logical_clock 3"
echo "===================================================="

echo "----------------------------------------------------"
echo "Solution 3A : One process, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 3A.dot -config A.cfg logical_clock3.tla && dot -Tpng 3A.dot -o 3A.png

echo "----------------------------------------------------"
echo "Solution 3B : Two processes, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 3B.dot -config B.cfg logical_clock3.tla && dot -Tpng 3B.dot -o 3B.png

echo "----------------------------------------------------"
echo "Solution 3C : Three processes, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 3C.dot -config C.cfg logical_clock3.tla && dot -Tpng 3C.dot -o 3C.png

echo "===================================================="
echo " logical_clock 4"
echo "===================================================="

echo "----------------------------------------------------"
echo "Solution 4A : One process, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 4A.dot -config A.cfg logical_clock4.tla && dot -Tpng 4A.dot -o 4A.png

echo "----------------------------------------------------"
echo "Solution 4B : Two processes, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 4B.dot -config B.cfg logical_clock4.tla && dot -Tpng 4B.dot -o 4B.png

echo "----------------------------------------------------"
echo "Solution 4C : Three processes, no reset of inbox"
echo "----------------------------------------------------"
tlc -dump dot 4C.dot -config C.cfg logical_clock4.tla && dot -Tpng 4C.dot -o 4C.png

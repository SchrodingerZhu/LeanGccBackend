SYSTEM=$1
GCCJIT=$2

for i in {0..100}; do
  INPUTS=$(shuf -i 0-10000 -n $i)
  SYSTEM_RESULT=$(./$SYSTEM $INPUTS)
  GCCJIT_RESULT=$(./$GCCJIT $INPUTS)
  if [ "$SYSTEM_RESULT" != "$GCCJIT_RESULT" ]; then
    echo "Error: $SYSTEM_RESULT != $GCCJIT_RESULT"
    exit 1
  fi
done

SYSTEM=$1
GCCJIT=$2

for i in {0..100}; do
  A=(shuf -i 0-18446744073709551614 -n 2500)
  SYSTEM_RESULT=$(./$SYSTEM $A)
  GCCJIT_RESULT=$(./$GCCJIT $A)
  if [ "$SYSTEM_RESULT" != "$GCCJIT_RESULT" ]; then
    echo "Error: $SYSTEM_RESULT != $GCCJIT_RESULT"
    exit 1
  fi
done

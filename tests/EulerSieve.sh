SYSTEM=$1
GCCJIT=$2

for i in {1..1000}; do
  SYSTEM_RESULT=$(./$SYSTEM $i)
  GCCJIT_RESULT=$(./$GCCJIT $i)
  if [ "$SYSTEM_RESULT" != "$GCCJIT_RESULT" ]; then
    echo "Error: $SYSTEM_RESULT != $GCCJIT_RESULT"
    exit 1
  fi
done
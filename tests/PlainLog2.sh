SYSTEM=$1
GCCJIT=$2

for i in {0..100}; do
  A=$(shuf -i 0-255 -n 1)
  B=$(shuf -i 0-65535 -n 1)
  C=$(shuf -i 0-4294967295 -n 1)
  D=$(shuf -i 0-18446744073709551614 -n 1)
  if [ `getconf LONG_BIT` = "64" ]
  then
    E=$(shuf -i 0-18446744073709551614 -n 1)
  else
    E=$(shuf -i 0-4294967295 -n 1)
  fi
  SYSTEM_RESULT=$(./$SYSTEM $A $B $C $D $E)
  GCCJIT_RESULT=$(./$GCCJIT $A $B $C $D $E)
  if [ "$SYSTEM_RESULT" != "$GCCJIT_RESULT" ]; then
    echo "Error: $SYSTEM_RESULT != $GCCJIT_RESULT"
    exit 1
  fi
done

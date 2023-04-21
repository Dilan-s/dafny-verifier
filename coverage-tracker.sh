#!/bin/bash

echo "PID: $$"
trap 'kill -9 $$' SIGINT

npm install bignumber.js

javac -cp src/main/java/ -d ./out/ src/main/java/Main/GenerateProgram.java src/main/java/Main/CompareOutputs.java

directory=$(pwd)

cd src/main/dafny_compiler/dafny/Binaries
dafny_binary=$(pwd)

cd "$directory"

x=0
while [ $x -le 0 ]; do
  cd "$directory"

  echo "Test number $x"
  java -cp out/ Main.GenerateProgram $x
  if [ $? -ne 0 ]
  then
    echo "Failed to create dafny file in $t seconds"
    x=$(( $x + 1 ))
    continue;
  fi
#  cp test.dfy tests/"test$x.dfy"
  # css
  #./src/main/dafny_compiler/dafny/Binaries/Dafny /noVerify /compileTarget:cs /spillTargetCode:3 test.dfy

  for file in tests/*.dfy
  do
    echo "Attempting to run $file"

    # GO
    cd "$dafny_binary"
    echo "coverlet . --target \"dotnet\" --targetargs \"Dafny.dll /noVerify /compile:2 /compileTarget:go ../../../../../"$file" /out:/tmp/dv\" -f json --merge-with \"../../../../../coverage/\"" | bash

    # js
    cd "$dafny_binary"
    echo "coverlet . --target \"dotnet\" --targetargs \"Dafny.dll /noVerify /compile:2 /compileTarget:js ../../../../../"$file" /out:/tmp/dv\" -f json --merge-with \"../../../../../coverage/\"" | bash

    # java
    cd "$dafny_binary"
    echo "coverlet . --target \"dotnet\" --targetargs \"Dafny.dll /noVerify /compile:2 /compileTarget:java ../../../../../"$file" /out:/tmp/dv\" -f json --merge-with \"../../../../../coverage/\"" | bash

    # py
    cd "$dafny_binary"
    echo "coverlet . --target \"dotnet\" --targetargs \"Dafny.dll /noVerify /compile:2 /compileTarget:py ../../../../../"$file" /out:/tmp/dv\" -f json --merge-with \"../../../../../coverage/\"" | bash

    cd "$directory"
  done

  rm -rf tests/* || true
  x=$(( $x + 1 ))

done

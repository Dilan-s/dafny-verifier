#!/bin/bash

echo "PID: $$"
trap 'kill -9 $$' SIGINT

npm install bignumber.js

rm -rf outputs || true
rm -rf errors || true
rm -rf tests || true
rm -rf tests-minimized || true
rm -rf tests-incorrect || true

mkdir outputs || true
mkdir errors || true
mkdir tests || true
mkdir tests-minimized || true
mkdir tests-incorrect || true


javac -cp src/main/java/ -d ./out/ src/main/java/Main/ExpectedProgramGeneration.java

directory=$(pwd)
rm -rf coverage || true
mkdir coverage


cd src/main/dafny_compiler/dafny/Binaries
dafny_dir=$(pwd)

cd "$directory"

x=0
while [ true ]; do
  cd "$directory"

  echo "Test number $x"
  timeout --foreground 300 java -cp out/ Main.ExpectedProgramGeneration
  if [ $? -ne 0 ]
  then
    echo "Failed to create dafny file in $t seconds"
    x=$(( $x + 1 ))
    continue;
  fi

  for file in tests/*.dfy
  do
    echo "Attempting to run $file"
    cp $file test.dfy
    cp test.dfy "$dafny_dir/test.dfy"

    # GO
    cd "$dafny_dir"
    echo "GO File"
    coverlet . --target dotnet --targetargs "Dafny.dll /deleteCodeAfterRun:1 /compile:4 /compileTarget:go test.dfy" -f cobertura -f json --merge-with coverage.json

    # js
    cd "$dafny_dir"
    echo "JS File"
    coverlet . --target dotnet --targetargs "Dafny.dll /deleteCodeAfterRun:1 /compile:4 /compileTarget:js test.dfy" -f cobertura -f json --merge-with coverage.json

    # java
    cd "$dafny_dir"
    echo "JAVA File"
    coverlet . --target dotnet --targetargs "Dafny.dll /deleteCodeAfterRun:1 /compile:4 /compileTarget:java test.dfy" -f cobertura -f json --merge-with coverage.json

    # py
    cd "$dafny_dir"
    echo "PY File"
    coverlet . --target dotnet --targetargs "Dafny.dll /deleteCodeAfterRun:1 /compile:4 /compileTarget:py test.dfy" -f cobertura -f json --merge-with coverage.json

    # cs
    cd "$dafny_dir"
    echo "CS File"
    coverlet . --target dotnet --targetargs "Dafny.dll /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs test.dfy" -f cobertura -f json --merge-with coverage.json


    cd "$directory"
    rm -rf test.dfy "$dafny_dir/test.dfy" || true

  done

  cd "$dafny_dir"
  cp coverage.cobertura.xml "$directory/coverage/"

  rm -rf tests/* || true
  x=$(( $x + 1 ))

done


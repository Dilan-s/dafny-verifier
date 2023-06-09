#!/bin/bash

echo "PID: $$"
trap 'kill -9 $$' SIGINT

npm install bignumber.js

javac -cp src/main/java/ -d ./out/ src/main/java/Main/GenerateProgram.java src/main/java/Main/CompareOutputs.java

rm -rf outputs || true
rm -rf tests || true
rm -rf errors || true
rm -rf tests-minimized || true
rm -rf tests-incorrect || true

mkdir tests || true
mkdir tests-minimized || true
mkdir tests-incorrect || true
mkdir outputs || true
mkdir errors || true
mkdir errors/verificationErrors
mkdir errors/compErrors
touch errors/compErrors/go.txt
touch errors/compErrors/java.txt
touch errors/compErrors/js.txt
touch errors/compErrors/py.txt
touch errors/compErrors/cs.txt



directory=$(pwd)

t=180
x=0
while [ true ]; do
  cd "$directory"

  echo "Test number $x"
  echo "Test number $x" >> errors/compErrors/go.txt
  echo "Test number $x" >> errors/compErrors/js.txt
  echo "Test number $x" >> errors/compErrors/java.txt
  echo "Test number $x" >> errors/compErrors/py.txt
  echo "Test number $x" >> errors/compErrors/cs.txt

  cd "$directory"
  timeout -s SIGKILL $t java -cp out/ Main.GenerateProgram $x
  if [ $? -ne 0 ]
  then
    echo "Failed to create dafny file in $t seconds"
    x=$(( $x + 1 ))
    continue;
  fi

  cd "$directory"
  y=0
  if [ "$(ls -A tests-minimized/)" ];
  then
    for file in tests-minimized/*.dfy
    do
      echo "Expecting validation to succeed for $file"

      timeout -s SIGKILL $t Dafny verify $file > tmp.txt 2>&1
      if [ $? -eq 4 ]
      then
        echo "Verification error found in test $x - correct validation of the file $file"
        mkdir "errors/verificationErrors/$x" || true
        mkdir "errors/verificationErrors/$x/correct" || true
        cp $file "errors/verificationErrors/$x/correct/test-$y.dfy"
        cat tmp.txt > "errors/verificationErrors/$x/correct/verificationOutput-$y.txt"
      fi
      rm -rf tmp.txt || true
      y=$(( $y + 1))
    done
  fi

  cd "$directory"
  y=0
  if [ "$(ls -A tests-incorrect/)" ];
  then
    for file in tests-incorrect/*.dfy
    do
      echo "Expecting validation to fail for $file"

      timeout -s SIGKILL $t Dafny verify $file > tmp.txt 2>&1
      code=$?
      if [[ $code -ne 4 && $code -lt 5 ]]
      then
        echo "Verification error found in test $x - incorrect validation of file $file"
        mkdir "errors/verificationErrors/$x" || true
        mkdir "errors/verificationErrors/$x/incorrect" || true
        cp $file "errors/verificationErrors/$x/incorrect/test-$y.dfy"
        cat tmp.txt > "errors/verificationErrors/$x/incorrect/verificationOutput-$y.txt"
      fi
      rm -rf tmp.txt || true
      y=$(( $y + 1))
    done
  fi

  cd "$directory"
  y=0
  if [ "$(ls -A tests/)" ];
  then
    for file in tests/*.dfy
    do
      echo "Attempting to run $file"
      cp "$file" test.dfy

      # GO
      cd "$directory"
      timeout -s SIGKILL $t Dafny /noVerify /compileTarget:go /compile:2 /compileVerbose:0 test.dfy > tmp.txt 2>>errors/compErrors/go.txt
      if [ $? -eq 0 ]
      then
        echo "Created GO files"
        ./test > "outputs/output-go-$y.txt" 2>>errors/compErrors/go.txt
        rm -rf test || true
        rm -rf test-go || true
      else
        rm -rf test || true
        rm -rf test-go || true
        echo "Failed to convert to GO in $t seconds"
      fi

      # js
      cd "$directory"
      timeout -s SIGKILL $t Dafny /noVerify /compileTarget:js /compile:2 /compileVerbose:0 test.dfy > tmp.txt 2>>errors/compErrors/js.txt
      if [ $? -eq 0 ]
      then
        echo "Created JS files"
        node test.js > "outputs/output-js-$y.txt" 2>>errors/compErrors/js.txt
        rm -rf test.js || true
      else
        rm -rf test.js || true
        echo "Failed to convert to JS in $t seconds"
      fi

      # java
      cd "$directory"
      timeout -s SIGKILL $t Dafny /noVerify /compileTarget:java /compile:2 /compileVerbose:0 /unicodeChar:0 test.dfy  > tmp.txt 2>>errors/compErrors/java.txt
      if [ $? -eq 0 ]
      then
        echo "Created Java files"
        java -jar test.jar > "outputs/output-java-$y.txt" 2>>errors/compErrors/java.txt
        rm -rf test.jar || true
        rm -rf test-java || true
      else
        rm -rf test.jar || true
        rm -rf test-java || true
        echo "Failed to convert to Java in $t seconds"
      fi

      # py
      cd "$directory"
      timeout -s SIGKILL $t Dafny /noVerify /compileTarget:py /compile:2 /compileVerbose:0 test.dfy > tmp.txt  2>>errors/compErrors/py.txt
      if [ $? -eq 0 ]
      then
        echo "Created Python files"
        python3 test-py/test.py > "outputs/output-py-$y.txt" 2>>errors/compErrors/py.txt
        rm -rf test-py || true
      else
        rm -rf test-py || true
        echo "Failed to convert to Python in $t seconds"
      fi

      # cs
      cd "$directory"
      timeout -s SIGKILL $t Dafny /noVerify /compileTarget:cs /compile:2 /compileVerbose:0 test.dfy > tmp.txt  2>>errors/compErrors/cs.txt
      if [ $? -eq 0 ]
      then
        echo "Created CS files"
        dotnet test.dll > "outputs/output-cs-$y.txt" 2>>errors/compErrors/cs.txt
        rm -rf test.dll test.runtimeconfig.json || true
      else
        rm -rf test.dll test.runtimeconfig.json || true
        echo "Failed to convert to CS in $t seconds"
      fi

      rm -rf test.dfy || true
      rm -rf tmp.txt || true
      y=$(( $y + 1))
    done
  fi
  java -cp out/ Main.CompareOutputs $x "./outputs"
  if [ $? -eq 1 ]
  then
    mkdir "errors/$x"
    mkdir "errors/$x/outputs"
    mkdir "errors/$x/tests"
    cp outputs/* "errors/$x/outputs"
    cp tests/* "errors/$x/tests"
  fi

  rm -rf tests/* || true
  rm -rf outputs/* || true
  rm -rf tests-minimized/* || true
  rm -rf tests-incorrect/* || true
  x=$(( $x + 1 ))

done

rm -rf test.dfy tmp.txt || true
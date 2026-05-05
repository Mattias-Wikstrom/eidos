#!/bin/sh

START_DIR="$(pwd)"

echo "Running in directory:"
pwd

echo "Running as:"
whoami
cd ~
echo "Home directory:"
pwd

cd ~/.cabal/store || exit 1
zip -r -q cabal-store.zip ghc-9.4.7/ || exit 1

cp cabal-store.zip "$START_DIR"/ || exit 1

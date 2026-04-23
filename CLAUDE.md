This repo is meant to contain a compiler written in Haskell for a language called Eidos.

I created a zip of my Cabal store by running the create_cabal_store_zip.sh shell script. It should be extracted to /root/.cabal/store/ghc-9.4.7/ on the target machine if you are root. The store contains packages compiled with GHC 9.4.7 and has a package.db directory with .conf files inside.

Files that will give you context:
  readme.MD 
  eidos-skill.skill 
  implicit.txt
  reflection.txt

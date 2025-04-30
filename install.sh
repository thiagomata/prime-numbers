rm -f sbt-stainless.zip
wget https://github.com/epfl-lara/stainless/releases/download/v0.9.8.9/sbt-stainless.zip
rm -rf project
rm -rf stainless
unzip sbt-stainless.zip

wget https://github.com/epfl-lara/stainless/releases/download/v0.9.8.8/stainless-dotty-standalone-0.9.8.8-linux.zip
unzip stainless-dotty-standalone-*
cp stainless-dotty-standalone-*/lib/stainess-library.jar project/lib/
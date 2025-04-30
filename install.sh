if [ ! -f "sbt-stainless.zip" ]; then
  wget https://github.com/epfl-lara/stainless/releases/download/v0.9.8.9/sbt-stainless.zip
fi
rm -rf project
rm -rf stainless
unzip sbt-stainless.zip

if [ ! -f "stainless-dotty-standalone-0.9.8.8.zip" ]; then
  wget https://github.com/epfl-lara/stainless/releases/download/v0.9.8.8/stainless-dotty-standalone-0.9.8.8-linux.zip
  mv stainless-dotty-standalone-0.9.8.8-linux.zip stainless-dotty-standalone-0.9.8.8.zip
fi
rm -rf stainless-dotty-standalone-0.9.8.8
unzip stainless-dotty-standalone-0.9.8.8.zip -d stainless-dotty-standalone-0.9.8.8
rm -rf project/lib/stainess-library.jar
cp ./stainless-dotty-standalone-0.9.8.8/lib/stainless-library.jar project/lib/

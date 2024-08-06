# Comparing Prime Number Sequences

This project compares prime number sequence implementations returning some metrics.
It also have a version of the Prime Number using the Sequences translated to Typescript.
I should create a better explanation of what is that and how that works.

# How to run this

After `npm install`

1. To Build `npm run build`
2. To Clean Artifacts `npm run clean`
3. To Test `npm run test`
4. To Lint `npm run lint`
5. To Buld and Watch when you make changes `npm run watch`

# Debugging with Visual Studio Code

1. Set a breakpoint in your code ending in `.ts` or your test ending in `.spec.ts`
2. Run Either `src/index.ts` or `All Tests` in the debug pane. 

# Running the Benchmark

This should become a separated project in the future.

## Compare percentile execution times of different commands
```shell script
node dist/index.js get-metrics \
  --times 20 \
  --commands "sleep 1; ls -lha | md5sum " \
  --commands "echo 1"  \
   --show-as-table \
   --show-as-json
```

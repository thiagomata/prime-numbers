const yargs = require('yargs');

export interface IRunExperimentSettings {
  commands: string[],
  names: string[],
  times: number,
  percentiles: number[],
  getEachExecutionResult: boolean,
  getEachExecutionTime: boolean,
  showAsTable: boolean,
  showAsJson: boolean
}

export const getRunExperimentSettings = (): IRunExperimentSettings => {
  return yargs
    .usage('Usage: $0 <command> [options]')
    .command('run', 'run command many times and create the expected outputs')
    .example('$0 run --get-result --get-execution-time --command "ls -lha | wc -l" --times 10 --show-as-table', 'Run the command 10 times and return the metrics as table')
    .option('commands', {
      describe: 'Commands to be evaluated',
      type: 'array',
      demand: true,
      requiresArg: true
    })
    .option('get-each-execution-result', {
      describe: 'Return the result of each execution',
      requiresArg: false
    })
    .option('get-each-execution-time', {
      describe: 'Return the result of each execution',
      requiresArg: false
    })
    .option('show-as-table', {
      describe: 'Show the experiments result as table',
      requiresArg: false
    })
    .option('show-as-json', {
      describe: 'Show the experiments result as json',
      requiresArg: false
    })
    .option('names', {
      describe: 'Names of the commands',
      type: 'array',
      demand: false,
      requiresArg: true
    })
    .option('percentiles', {
      describe: 'Name of the current command',
      type: 'number',
      demand: false,
      default: [50, 90, 95, 99],
      requiresArg: true
    })
    .option('times', {
      describe: 'How many times should we run the command',
      type: 'number',
      nargs: 1,
      demand: false,
      default: 10
    })
    .help('help')
    .epilog('Just for fun. free for use with not warranties.')
    .argv;
}


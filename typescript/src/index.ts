const { exec } = require('child_process')

export class ExperimentResult {
  result: String;
  time: number  
}

interface IExperiment {
  run(): Promise<ExperimentResult> {
  }
} 

/**
 * Encapsulte a single run of a command with the time metrics
 */
export class Experiment implements IExperiment{
  
  name: string;
  command: string;

  constructor(name: string, command: string) {
    this.name = name;
    this.command = command;
  }

  run(): Promise<ExperimentResult> {
    return new Promise<ExperimentResult>((resolve, reject) => {
      let startTime = Date.now();
      exec(this.command, (error: Error, stdout: string, stderr: string) => {
        let endTime = Date.now();
        if (error !== null ) {
          reject(error);
        }
        if(stderr !== null && stderr != "" ) {
          reject(new Error(stderr));
        }
        resolve({
          result: stdout.trim(),
          time: endTime - startTime
        })
      });
    });    
  }
}

class RepeatedExperiment {

  repeat: number;
  experiment: IExperiment;
  results: Array<ExperimentResult> = [];

  constructor(experiment: IExperiment, repeat: number) {
    this.repeat = repeat;
    this.experiment = experiment;
  }

  run(): Promise<Array<ExperimentResult>> {
    return this.runLoop(this.repeat);
  }

  async runLoop(loopCounter: number): Promise<Array<ExperimentResult>> {
    console.log("loopCounter = ",loopCounter);
    const experimentResult = await this.experiment.run();
    if (loopCounter <= 0) {
      return [experimentResult];
    }
    const experimentResults = await this.runLoop(loopCounter - 1);
    return experimentResults.concat(experimentResult);
  } 
}

let experiment = new Experiment("test", "ls | wc -l");
let repeatedExperiment = new RepeatedExperiment(experiment,5);
repeatedExperiment.run().then(result => {
  console.log(result);
}).catch(error => {
  console.error(error);
})
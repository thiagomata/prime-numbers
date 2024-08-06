import {Experiment} from "./Experiment";
import {RepeatedExperiment} from "./RepeatedExperiment";
import {ExperimentResult} from "./ExperimentResult";
import {IExperimentResult} from "./IExperimentResult";
import {IRunExperimentSettings} from "./RunExperimentSettings";
const cliProgress = require('cli-progress');

const percentile = require('percentile');

export interface IEachExecution {
  executionResult?: string,
  executionTime?: number
}

export interface IPercentile {
  [percentile: number]: number
}

export interface IRunResult {
  [command: string]: {
    executionResults?: IEachExecution[]
    percentiles?: IPercentile
  }
}

export interface IRunExperimentResult {
  [command: string]: IExperimentResult[]
}

export class RunExperiment {
  constructor(readonly settings: IRunExperimentSettings, readonly showProgress: boolean = true) {
    console.log(settings);
  }

  public async run() {
    const results = await this.geExperimentResults();
    const combinedResults: IRunResult = {}
    for ( let commandName in results ) {
      const commandResult = results[commandName];
      const runExperimentResult = this.extractExperimentResults(commandResult);
      const runPercentiles: IPercentile | undefined = this.extractPercentiles(commandResult);
      combinedResults[commandName] = {
        executionResults: runExperimentResult,
        percentiles: runPercentiles,
      }
    }
    if ( this.settings.showAsTable ) {
      this.showAsTable(combinedResults);
    }

    if ( this.settings.showAsJson ) {
      this.showAsJson(combinedResults);
    }

    return combinedResults;
  }

  private extractExperimentResults(results: Array<ExperimentResult>): IEachExecution[] | undefined {
    if ( !this.settings.getEachExecutionResult && !this.settings.getEachExecutionTime ) {
      return undefined;
    }
    const settings = this.settings;
    let runExperimentResult = results.map(
      (experimentResult: IExperimentResult): IEachExecution => {
        let executionDetails: IEachExecution = {};
        if (settings.getEachExecutionResult) {
          executionDetails.executionResult = experimentResult.result
        }
        if (settings.getEachExecutionTime) {
          executionDetails.executionTime = experimentResult.time
        }
        return executionDetails;
      }
    )
    return runExperimentResult;
  }

  private async geExperimentResults(): Promise<IRunExperimentResult> {
    let results: IRunExperimentResult = {};

    for ( let i = 0; i < this.settings.commands.length; i++ ) {
      const command = this.settings.commands[i];
      const commandName = this.getCommandName(i);
      console.log("command = ", command);
      console.log("command Name = ", commandName);
      const experiment = new Experiment(commandName, command);
      const repeatedExperiment = new RepeatedExperiment(experiment, this.settings.times);
      let onExperimentProgress = () => {};
      let onExperimentEnd = () => {}
      if ( this.showProgress ) {
        const experimentBarProgress = new cliProgress.SingleBar({}, cliProgress.Presets.shades_classic);
        experimentBarProgress.start(this.settings.times)
        onExperimentProgress = experimentBarProgress.increment.bind(experimentBarProgress);
        onExperimentEnd = experimentBarProgress.stop.bind(experimentBarProgress);
      }
      const experimentResult: Array<ExperimentResult> = await repeatedExperiment.run(
        (progress: number) => {
          onExperimentProgress();
        }
      );
      onExperimentEnd();
      results[commandName] = experimentResult;
    }
    return results;
  }

  private getCommandName(i: number) {
    return this.hasCommandName(i) ? this.settings.names[i] : this.settings.commands[i];
  }

  private hasCommandName(i: number): boolean {
    if ( ! this.settings.names ) {
      return false;
    }
    if ( this.settings.names.length <= i ) {
      return false;
    }
    if ( ! this.settings.names[i] ) {
      return false;
    }
    return true;
  }

  private showAsTable(runResult: IRunResult) {

    let combinedPercentiles = {}
    for ( const command in runResult ) {
      if ( runResult[command].executionResults ) {
        console.log("## Experiment Results");
        console.table(runResult[command].executionResults);
      }
      if ( runResult[command].percentiles ) {
        combinedPercentiles[command] = runResult[command].percentiles;
      }
    }
    console.log("## Percentiles");
    console.table(combinedPercentiles);
  }

  private showAsJson(runResult: IRunResult) {
    console.log( JSON.stringify(runResult, null, 2));
  }

  private extractPercentiles(results: Array<ExperimentResult>): IPercentile | undefined {
    if ( ! this.settings.percentiles || this.settings.percentiles.length === 0 ) {
      return undefined;
    }
    const timeResults = results.map( r => r.time );
    let result = {
      max: timeResults.reduce((a, b) => Math.max(a, b)),
      min: timeResults.reduce((a, b) => Math.min(a, b)),
    };
    this.settings.percentiles.forEach(
      p => {
        result[p] = percentile(
            p,
            timeResults,
          )
      }
    )
    return result;
  }
}

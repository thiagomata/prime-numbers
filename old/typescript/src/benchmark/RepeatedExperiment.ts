import {IExperiment} from "./IExperiment";
import {ExperimentResult} from "./ExperimentResult";

export class RepeatedExperiment {

  repeat: number;
  experiment: IExperiment;
  results: Array<ExperimentResult> = [];

  constructor(experiment: IExperiment, repeat: number) {
    this.repeat = repeat;
    this.experiment = experiment;
  }

  run(onLoop: (integer) => void = (x) => {}): Promise<Array<ExperimentResult>> {
    return this.runLoop(this.repeat, onLoop);
  }

  async runLoop(loopCounter: number, onLoop: (integer) => void): Promise<Array<ExperimentResult>> {
    onLoop(loopCounter);
    const experimentResult = await this.experiment.run();
    if (loopCounter <= 0) {
      return [experimentResult];
    }
    const experimentResults = await this.runLoop(loopCounter - 1, onLoop);
    return experimentResults.concat(experimentResult);
  }
}

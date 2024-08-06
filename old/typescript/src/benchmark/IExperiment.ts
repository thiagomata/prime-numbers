import {IExperimentResult} from "./IExperimentResult";

export interface IExperiment {
  run(): Promise<IExperimentResult>
}

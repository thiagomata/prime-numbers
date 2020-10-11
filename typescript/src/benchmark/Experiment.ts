import {IExperiment} from "./IExperiment";
import {IExperimentResult} from "./IExperimentResult";
import {exec} from "child_process";

/**
 * Encapsulte a single run of a command with the time metrics
 */
export class Experiment implements IExperiment {

  private readonly name: string;
  private readonly command: string;

  constructor(name: string, command: string) {
    this.name = name;
    this.command = command;
  }

  run(): Promise<IExperimentResult> {
    return new Promise<IExperimentResult>((resolve, reject) => {
      let startTime = Date.now();
      exec(this.command, (error: Error, stdout: string, stderr: string) => {
        let endTime = Date.now();
        if (error !== null) {
          reject(error);
        }
        if (stderr !== null && stderr !== "") {
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

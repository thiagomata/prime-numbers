import {Experiment} from "./benchmark/Experiment";
import {RepeatedExperiment} from "./benchmark/RepeatedExperiment";
import {IEachExecution, RunExperiment} from "./benchmark/RunExperiment";
import {getRunExperimentSettings} from "./benchmark/RunExperimentSettings";

const { exec } = require('child_process')

const runExperiment = new RunExperiment( getRunExperimentSettings() );
runExperiment.run();

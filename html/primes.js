// adding some powers to the array
Array.prototype.sum = function () {
  return this.reduce((a, b) => a + b, 0);
};

Array.prototype.circular = function (pos) {
  if (pos >= 0 && pos < this.length) {
    return this[pos];
  }
  if (pos < 0) {
    pos += this.length * Math.abs(pos);
  }
  return this[pos % this.length];
};

Array.prototype.first = function() {
  return this[0]; 
}

Array.prototype.last = function() {
  return this[this.length - 1];
}


Array.prototype.rotateLeft = function () {
  let last = this[this.length - 1];
  return [last].concat(this.slice(0, this.length - 1));
};

Array.prototype.rotateRigth = function () {
  let first = this[0];
  return this.slice(1, this.length).concat(first);
};

/*
 * a sequence is a infinite repetition of steps in loop after the previous numbers  
 */
function Sequence(settings) {
  this.step = settings.step;
  this.previousStep = settings.previousStep;
  this.currentNumber = settings.currentNumber;
  this.previousNumbers = settings.previousNumbers;
}

/**
 * Show some elements of the current sequence
 */
Sequence.prototype.preview = function (size = 100) {
  let preview = [].concat(this.previousNumbers);
  let circular = 0;
  for (let i = preview.length; i < size; i++) {
    preview[i] = preview[i - 1] + this.step.circular(circular);
    circular++;
  }
  return preview;
};

Sequence.prototype.until = function (last = 100) {
  let preview = [].concat(this.previousNumbers);
  if( preview.last() >= last ) {
    return x.filter( v => v <= last );
  }
  
  let circular = 0;
  let i = preview.length
  while (preview.last() < last ) {
    preview[i] = preview[i - 1] + this.step.circular(circular);
    circular++;
    i++
  }
  return preview.filter( p => p <= last );
};

/**
 * Concatenate from the current steps those that added to the next number 
 * could be multiple of the current number.
 *
 * After adding the 2, we don't want any multiple of 2 in the sequence that starts with 3 ( the next number )
 * After adding the 3, we don't want any multiple of 3 in the sequence that starts with 5 ( the next number )
 */
function reduceStep(buildingStep, currentNumber, nextNumber) {
  let acc = nextNumber;
  let pass = 0;
  let result = [];
  buildingStep.forEach(
      (value) => {
        acc += value;
        if( acc % currentNumber === 0 ) {
          pass += value;
        } else {
          value += pass;
          pass = 0;
          result.push(value);
        }
      }
  )
  if ( pass !== 0) {
    // we could not find a solution that avoid the multiples of the currentNumber
    // combining the current steps
    throw new Error("unable to find a possible answer to the reduce step " + pass);
  }
  return result;
}

Sequence.prototype.getNextNumber = function () {
  return this.currentNumber + this.step[0];
}
/**
 * Create the next sequence based in the current one, avoiding the multiples
 * of the new element
 */
Sequence.prototype.next = function () {
  let previousStep = this.step;
  let buildingStep = this.step.rotateRigth();
  let nextNumber = this.getNextNumber();
  let addStep = [].concat(buildingStep);
  let loopStep = [];
  do {
    loopStep = loopStep.concat(addStep);
    let totalStep = loopStep.sum();
    if (totalStep % this.currentNumber != 0) {
      continue;
    }
    loopStep = reduceStep(loopStep, this.currentNumber, nextNumber);
  } while (loopStep.sum() % this.currentNumber !== 0);

  return new Sequence({
    step: loopStep,
    previousStep: previousStep,
    currentNumber: nextNumber,
    previousNumbers: this.previousNumbers.concat(nextNumber)
  });
};

Sequence.createFirst = function () {
  return new Sequence({
    step: [1],
    previousStep: [0],
    currentNumber: 2,
    previousNumbers: [2]
  });
};

window.loadSequences = function loadSequences() {
  
  let table = document.createElement("table");
  let sequence = null;
  let loadSequences = 6;
  for (let i = 0; i < loadSequences; i++) {
    if (sequence === null) {
      sequence = Sequence.createFirst();
    } else {
      sequence = sequence.next();
    }
    let row = document.createElement("tr");
    row.className = "values"
    let cel_header = document.createElement("td");
    cel_header.innerHTML = 'sequence';
    row.appendChild(cel_header);
    let steps = document.createElement("tr");
    steps.className = "steps"
    let step_header = document.createElement("td");
    step_header.innerHTML = 'steps';
    step_header.title = sequence.step;
    steps.appendChild(step_header);
    let preview = sequence.preview(42);
    preview.forEach((value, key) => {
      let isPrevious = sequence.previousNumbers.indexOf(value) > -1;
      let cel = document.createElement("td");
      cel.innerHTML = value;
      if( isPrevious ) {
        cel.className = " previous "      
      } else {
        cel.className = " seqvalue "      
        cel.title =
        preview[key - 1] + " + " +
        sequence.step.circular(key - sequence.previousNumbers.length);
      }

      row.appendChild(cel);
      let step = document.createElement("td");
      step.innerHTML = sequence.step.circular(key - sequence.previousNumbers.length);
      if( isPrevious ) {
        step.className = " previous "      
      } else {
        step.className = " seqvalue "
      }
      step.className += " seq" + (Math.floor( (key + sequence.step.length - sequence.previousNumbers.length) / sequence.step.length ) % 5);
      steps.appendChild(step);
    });
    table.appendChild(steps);
    table.appendChild(row);
  }

  document.body.appendChild(table);


  let maxSafeNumber =  ( sequence.getNextNumber() * sequence.getNextNumber() - 1 );
  let divExplain = document.createElement("div");
  divExplain.className = "explain";
  divExplain.innerHTML = "This " + loadSequences + "# sequence is able to filter out all the multiples of " + sequence.previousNumbers + " ." +
    "Ensuring to have only prime numbers until " +  maxSafeNumber + ". It also reduce the number of elements to search for prime numbers in " + Math.round( 100 - 100 * sequence.step.length / sequence.step.sum() ) + "% after that.";
  document.body.appendChild(divExplain);

  let div = document.createElement("div");
  div.className = "manyNumbers"
  div.innerHTML = "The first 200 elements of that sequence are: <code>" + sequence.preview(200).map( x => " " + x) + "</code>";
  document.body.appendChild(div);

  let seq = document.createElement("div");
  seq.className = "manyNumbers"
  seq.innerHTML = "The steps of the " + loadSequences + "# sequence are: <code>" + sequence.step.map( x => " " + x) + "</code>";
  document.body.appendChild(seq);
}

////////////////// some performance tests //////////////////////////////

/*
 * classic prime calculation, avoiding pair numbers
 */
function isPrime(n,countIsPrime) {
  countIsPrime.count++;
  if( n == 2 ) {
    return true;
  }
  countIsPrime.calculate++;
  // console.log('calculate',n,'%',2);
  if (n % 2 == 0 ) {
    return false;
  }
  for(let i = 3; i <= Math.sqrt(n); i+=2 ) {
    countIsPrime.calculate++;
    // console.log('calculate',n,'%',i);
    if( n % i === 0 ) {
      return false;
    }
  }
  return true;
}

/**
 * Calculate if the number is multiple of any element 
 * of the ordered list
 */
function isMultiple(n,elements,countIsPrime) {
  countIsPrime.count++;
  let nS = Math.sqrt(n);

  for(var i = 0; i < elements.length; i++ ) {
    let element = elements[i];
    if (element > nS ) {
      return false;
    }
    if( n % element === 0 ) {
      return true;
    }
  }
  return false;

  // return elements
  //   .filter(
  //     element => element <= nS
  //   )
  //   .find(
  //     element => {
  //       countIsPrime.calculate++;
  //       // console.log('calculate',n,'%',element);
  //       return n % element === 0;
  //     }
  // ) !== undefined;
}

/**
 * Classic prime sequence calculation
 */
function allPrimesUntil(x) {
  let start = new Date();
  let primes = [2];
  let countIsPrime = {count:0,calculate:0};
  for( let i = 3; i <= x;  i+=2) {
    if( isPrime(i, countIsPrime) ) {
      primes.push(i);
    }
  }
  let finish = new Date();
  // console.log(finish - start, "all primes until time", x)
  // console.log("countIsPrime", countIsPrime);
  return {
    primes:primes,
    countIsPrime:countIsPrime,
    time: finish - start,
  }; 
}

/**
 * Prime sequence using previous values
 */
function allPrimesUntil2(x) {
  let start = new Date();
  let primes = [2];
  let countIsPrime = {count:0,calculate:0};
  for( let i = 3; i <= x;  i+=2) {
    if( !isMultiple(i, primes, countIsPrime) ) {
      // if(!isPrime(i,countIsPrime)){
      //   console.log('bad i ',i,primes);
      //   throw new Error("sad");
      // }
      primes.push(i);
    }
  }
  let finish = new Date();
  // console.log(finish - start, "all primes until time", x)
  // console.log("countIsPrime 2", countIsPrime);
  return {
    primes:primes,
    countIsPrime:countIsPrime,
    time: finish - start,
  };
}

/**
 * Use the sequence only to sherry pick the elements
 * then, use the classic prime process
 */
function allPrimesUntilSeq(x, seq) {
  let start = new Date();
  let countIsPrime = {count:0,calculate:0};
  let primes = [];
  seq.previousNumbers.forEach(
    p => {
      if (isPrime(p,countIsPrime) && p <= x  ) {
        primes.push(p);
      }
    }
  )
  
  let currentNumber = seq.previousNumbers.last();
  let circular = 0;

  while(x >= currentNumber) {
    currentNumber += seq.step.circular(circular);
    circular++;
    if( currentNumber <= x && isPrime(currentNumber, countIsPrime) ) {
      primes.push(currentNumber);
    }
  }
  let finish = new Date();
  // console.log(finish - start, "all primes until seq time", x)
  // console.log("countIsPrime Seq", countIsPrime);
  return {
    primes:primes,
    countIsPrime:countIsPrime,
    time: finish - start,
  }; 
}

/**
 * Use the sequence to add the sure prime elements
 * Use the classic prime to the others
 */
function allPrimesUntilSeq2(x, seq) {
  let start = new Date();
  let primes = [];
  let countIsPrime = {count:0,calculate:0};
  seq.previousNumbers.forEach(
    p => {
      if (p <= x) {
        primes.push(p);
      }
    }
  )
  
  let lastPreviousSquared = seq.previousNumbers.last() * seq.previousNumbers.last();
  let currentNumber = seq.previousNumbers.last();
  let circular = 0;

  while(x >= currentNumber && currentNumber < lastPreviousSquared) {
    currentNumber += seq.step.circular(circular);
    circular++;
    if( currentNumber <= x ) {
      if ( currentNumber < lastPreviousSquared || isPrime(currentNumber, countIsPrime) ) {
        primes.push(currentNumber);
      }
    }
  }

  while(x >= currentNumber) {
    currentNumber += seq.step.circular(circular);
    circular++;
    if( currentNumber <= x ) {
      if(isPrime(currentNumber,countIsPrime)) {
        primes.push(currentNumber);
      }
    }
  }
  let finish = new Date();
  // console.log(finish - start, "all primes until seq time", x)
  // console.log("countIsPrime Seq 2", countIsPrime);
  return {
    primes:primes,
    countIsPrime:countIsPrime,
    time: finish - start,
  }; 
}

/**
 * Use the sequence to add the first sure prime elements
 * and use the prime list to check the next sherry pick element
 */
function allPrimesUntilSeq3(x, seq) {
  let start = new Date();
  let primes = [];
  let countIsPrime = {count:0,calculate:0};
  seq.previousNumbers.forEach(
    p => {
      if (p <= x) {
        primes.push(p);
      }
    }
  )
  
  let lastPreviousSquared = seq.previousNumbers.last() * seq.previousNumbers.last();
  let currentNumber = seq.previousNumbers.last();
  let circular = 0;

  while(x >= currentNumber && currentNumber < lastPreviousSquared) {
    currentNumber += seq.step.circular(circular);
    circular++;
    if( currentNumber <= x ) {
      if ( currentNumber < lastPreviousSquared || !isMultiple(currentNumber, primes, countIsPrime) ) {
        primes.push(currentNumber);
      }
    }
  }

  while(x >= currentNumber) {
    currentNumber += seq.step.circular(circular);
    circular++;
    if( currentNumber <= x ) {
      if(!isMultiple(currentNumber,primes,countIsPrime)) {
        primes.push(currentNumber);
      }
    }
  }
  let finish = new Date();
  // console.log(finish - start, "all primes until seq time", x)
  // console.log("countIsPrime", countIsPrime);
  return {
    primes:primes,
    countIsPrime:countIsPrime,
    time: finish - start,
  }; 
}

function compareVersions(n,seq) {
  let v1 = allPrimesUntil(n);
  let v2 = allPrimesUntil2(n);
  let v3 = allPrimesUntilSeq(n,seq);
  let v4 = allPrimesUntilSeq2(n,seq);
  let v5 = allPrimesUntilSeq3(n,seq);

  let maxTime  = Math.max(v1.time,  v2.time,  v3.time,  v4.time,  v5.time, 1);
  let maxCount = Math.max(
    v1.countIsPrime.count, 
    v2.countIsPrime.count, 
    v3.countIsPrime.count, 
    v4.countIsPrime.count, 
    v5.countIsPrime.count,
    1
  );

  // console.log('maxtime',maxTime);
  // console.log('maxCount',maxCount);

  return {
    time: {
      v1: v1.time,
      v2: v2.time,
      v3: v3.time,
      v4: v4.time,
      v5: v5.time 
    },
    timeNorm: {
      v1: v1.time * 100 / maxTime,
      v2: v2.time * 100 / maxTime,
      v3: v3.time * 100 / maxTime,
      v4: v4.time * 100 / maxTime,
      v5: v5.time * 100 / maxTime 
    },
    count: {
      v1: v1.countIsPrime.count,
      v2: v2.countIsPrime.count,
      v3: v3.countIsPrime.count,
      v4: v4.countIsPrime.count,
      v5: v5.countIsPrime.count,
    },
    countNorm: {
      v1: v1.countIsPrime.count * 100 / maxCount,
      v2: v2.countIsPrime.count * 100 / maxCount,
      v3: v3.countIsPrime.count * 100 / maxCount,
      v4: v4.countIsPrime.count * 100 / maxCount,
      v5: v5.countIsPrime.count * 100 / maxCount,
    },
    calculate: {
      v1: v1.countIsPrime.calculate,
      v2: v2.countIsPrime.calculate,
      v3: v3.countIsPrime.calculate,
      v4: v4.countIsPrime.calculate,
      v5: v5.countIsPrime.calculate,
    }
  }
}

s1 = Sequence.createFirst();
s2 = s1.next();
s3 = s2.next();
s4 = s3.next();
s5 = s4.next();
s6 = s5.next();
s7 = s6.next();

function runPerformanceTest(button) {
  debugger;
  console.log('start performance test');
  button.disabled = true;
  button.label = "Running...";
  button.value = "Running...";
  setTimeout(function(){
      var code = document.createElement("pre");
      // codepen has some restrictions about long executions.
      // try this in node to check the impact with bigger numbers
      code.innerHTML = JSON.stringify(compareVersions(1000000,s7));
      document.body.appendChild(code);
      button.label = "Run Performance Test";
      button.value = "Run Performance Test";
      button.disabled = false;
    },1);
}

function infiniteCompare() {
  let v = 1;
  while(true) {
    v *= 2;
    let c = compareVersions(v,s7);
    line = [v,c.timeNorm.v1,c.timeNorm.v2,c.timeNorm.v3,c.timeNorm.v4,c.timeNorm.v5].join(",");
    console.log(line);
  }
}


function compareVersionsv2v5(n,seq) {
  let v2 = allPrimesUntil2(n);
  let v5 = allPrimesUntilSeq3(n,seq);

  let maxTime  = Math.max(v2.time,v5.time, 1);
  let maxCount = Math.max(
    v2.countIsPrime.count, 
    v5.countIsPrime.count,
    1
  );

  // console.log('maxtime',maxTime);
  // console.log('maxCount',maxCount);

  return {
    time: {
      v2: v2.time,
      v5: v5.time, 
      v6: v6.time 
    },
    timeNorm: {
      v2: v2.time * 100 / maxTime,
      v5: v5.time * 100 / maxTime 
    },
    count: {
      v2: v2.countIsPrime.count,
      v5: v5.countIsPrime.count,
    },
    countNorm: {
      v2: v2.countIsPrime.count * 100 / maxCount,
      v5: v5.countIsPrime.count * 100 / maxCount,
    },
    calculate: {
      v2: v2.countIsPrime.calculate,
      v5: v5.countIsPrime.calculate,
    }
  }
}

  function vs6(n) {
    let start = new Date();
    let s =  Sequence.createFirst();
    
    let sqrtN = Math.sqrt(n);
    while(s.currentNumber <= sqrtN ) {
      s = s.next();
    }
    let primes = s.until(n);
    let finish = new Date();
    return {
      primes:primes,
      countIsPrime:0,
      time: finish - start,
      seq: s
    }; 
  }
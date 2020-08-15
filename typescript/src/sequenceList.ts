export class SequenceList extends Array<number> {

    first(): number {
        return this[0];
    }

    last(): number {
        return this[this.length - 1];
    }

    sum(): number {
        return this.reduce(
            (a,b) => a + b, 0
        );
    }

    concat(...items: (number | ConcatArray<number>)[]): SequenceList {
        return super.concat(...items) as SequenceList;
    }

    circular(pos: number): number{
        if (this.length == 0 ) {
            return undefined;
        }
        while (pos < 0) {
            pos += this.length * Math.abs(pos);
        }
        if (pos < this.length) {
            return this[pos];
        }
        return this[pos % this.length];
    }

    rotateLeft(): SequenceList {        
        return [this.last()]
            .concat(this.slice(0, this.length - 1)) as SequenceList;
    }

    rotateRight(): SequenceList {        
        return this.slice(1, this.length)
            .concat(this.first()) as SequenceList;
    }
}
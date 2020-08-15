import * as mocha from 'mocha'
import { expect } from 'chai'

import { SequenceList } from "../src/sequenceList";

describe('SequenceList Tests', function () {

    let sequenceList: SequenceList = null

    beforeEach(function () {
        sequenceList = new SequenceList(1,2,3);// as SequenceList;
    })

    it('Test first', function () {
        const first = sequenceList.first();
        expect(first).to.eq(1)
    })

    it('Test last', function () {
        const last = sequenceList.last()
        expect(last).to.eq(3)
    })

    it('Circular Negative', function() {
        const circular = sequenceList.circular(-1);
        expect(circular).to.eq(3)
    })

    it('Circular inbound', async function () {
        const circular = sequenceList.circular(1);
        expect(circular).to.eq(2)
    })

    it('Circular outbound', function () {
        const circular = sequenceList.circular(3);
        expect(circular).to.eq(1)
    })
});
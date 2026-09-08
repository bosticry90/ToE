"""Seven-record source execution with a separately checkable C03 physical DAG.

This does not upgrade the native-E or RV stage transcripts to fully verified
graphs. No independent scientific review or full acceptance is implied.
"""
from formal.python.toe.generic_runner import seven_record_source_candidate_v5 as previous
from formal.python.toe.generic_runner import c03_physical_dag_candidate_v1 as physical

c = previous.c


def compute(root=c.norm.ROOT):
    packet = previous.compute(root)
    fragment = physical.compute(root)
    c.require(c.E(packet['authoritative_outputs'][physical.p.ROOT_ID]) ==
              c.E(fragment['outputs'][physical.p.ROOT_ID]), 'C03_TRANSCRIPT_SCIENCE_MISMATCH')
    packet['schema_id'] = 'SEVEN_RECORD_WITH_C03_FINE_PHYSICAL_FRAGMENT_v1'
    packet['c03_physical_fragment'] = fragment
    packet['candidate_status'] = 'C03_FINE_PHYSICAL_FRAGMENT_IMPLEMENTED__FULL_QUALIFICATION_INCOMPLETE'
    packet['limitations'].append('C03 physical fragment has a separate operation checker; other output graphs remain incomplete.')
    return packet


if __name__ == '__main__':
    print(c.exact.canonical(compute()))

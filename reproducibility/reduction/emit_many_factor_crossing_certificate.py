"""Emit all 449 bounded-exception integer margins in ordinary kernel reduction."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def main():
    qa=json.loads((ROOT/'audit_many_factor_CI_crossing.json').read_text(encoding='utf8'))
    rows=qa['integer_margins'];assert len(rows)==449 and len(qa['complete_exception_profiles'])==3
    parts=[rows[i:i+256] for i in range(0,len(rows),256)]
    blocks=['import Mathlib\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace ManyFactorCrossingCertificate\n']
    for i,chunk in enumerate(parts):
        name='part'+str(i)
        blocks.append('def '+name+' : List ℤ := ['+', '.join(map(str,chunk))+']\n')
        blocks.append('theorem '+name+'_certificate : '+name+'.all (fun z => decide (0 ≤ z)) = true := by\n  decide\n')
    blocks.append('def rows : List ℤ := part0 ++ part1\n')
    blocks.append('theorem all_integer_margins : rows.all (fun z => decide (0 ≤ z)) = true := by\n  simp only [rows, List.all_append, part0_certificate, part1_certificate, Bool.and_self]\n')
    blocks.append('#print axioms all_integer_margins\n\nend ManyFactorCrossingCertificate\n')
    (ROOT/'ManyFactorCrossingCertificate.lean').write_text('\n'.join(blocks),encoding='utf8')
    print(json.dumps(dict(profiles=3,hosts=58,comparisons=770,distinct_margins=449,chunks=2)),flush=True)

if __name__=='__main__':main()

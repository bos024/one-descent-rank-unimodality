"""Emit the complete 119-profile bounded exception scalar certificate."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def main():
    qa=json.loads((ROOT/'audit_double_subdegree_CI_entrance.json').read_text(encoding='utf8'))
    rows=qa['integer_margins'];assert len(rows)==11087 and len(qa['complete_small_degree_profiles'])==119
    parts=[rows[i:i+384] for i in range(0,len(rows),384)]
    blocks=['import Mathlib\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\nnamespace DoubleSubdegreeCertificate\n']
    for i,chunk in enumerate(parts):
        name='part'+str(i)
        blocks.append('def '+name+' : List ℤ := ['+', '.join(map(str,chunk))+']\n')
        blocks.append('theorem '+name+'_certificate : '+name+'.all (fun z => decide (0 ≤ z)) = true := by\n  decide\n')
    blocks.append('def rows : List ℤ := '+' ++ '.join('part'+str(i) for i in range(len(parts)))+'\n')
    blocks.append('theorem all_integer_margins : rows.all (fun z => decide (0 ≤ z)) = true := by\n  simp only [rows, List.all_append, '+', '.join('part'+str(i)+'_certificate' for i in range(len(parts)))+', Bool.and_self]\n')
    blocks.append('#print axioms all_integer_margins\n\nend DoubleSubdegreeCertificate\n')
    (ROOT/'DoubleSubdegreeCertificate.lean').write_text('\n'.join(blocks),encoding='utf8')
    print(json.dumps(dict(profiles=119,hosts=1969,comparisons=21127,distinct_margins=len(rows),chunks=len(parts))),flush=True)

if __name__=='__main__':main()

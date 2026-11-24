"""Emit the complete215-context subdegree certificate in bounded Lean chunks."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def main():
    qa=json.loads((ROOT/'audit_subdegree_CI_entrance.json').read_text(encoding='utf8'))
    rows=qa['complete_small_scalar_margins'];assert len(rows)==11853
    source=(ROOT/'DividedCILaterSmallCertificate.lean').read_text(encoding='utf8')
    begin=source.index('def rows :');end=source.index('\n]\n',begin)+2
    prefix=source[:begin].replace('DividedCILaterSmallCertificate','SubdegreeCIChunkCertificate')
    suffix=source[end:].replace('DividedCILaterSmallCertificate','SubdegreeCIChunkCertificate')
    old_start=suffix.index('def actualStartupMargins :');old_end=suffix.index('\ntheorem complete_actual_startup_margins',old_start)
    integers=qa['complete_small_startup_integer_margins'];assert len(integers)==24
    suffix=suffix[:old_start]+'def actualStartupMargins : List ℤ := ['+', '.join(map(str,integers))+']\n'+suffix[old_end:]
    chunks=[rows[i:i+384] for i in range(0,len(rows),384)];blocks=[]
    for i,chunk in enumerate(chunks):
        name='part'+str(i)
        blocks.append('def '+name+' : List (ℤ × ℤ) := [\n'+',\n'.join('  ('+str(a)+', '+str(b)+')' for a,b in chunk)+'\n]\n')
        blocks.append('theorem '+name+'_certificate : '+name+'.all (fun r => decide (0 ≤ 10000000000000000*r.1+\n  (if 0 ≤ r.2 then 16180339887498948*r.2 else 16180339887498949*r.2))) = true := by\n  decide\n')
    blocks.append('def rows : List (ℤ × ℤ) := '+' ++ '.join('part'+str(i) for i in range(len(chunks)))+'\n')
    ebegin=suffix.index('theorem endpoint_certificate :');eend=suffix.index('\ntheorem golden_fine_interval',ebegin)
    new_endpoint='theorem endpoint_certificate :\n    rows.all (fun r => decide (0 ≤ 10000000000000000*r.1+\n      (if 0 ≤ r.2 then 16180339887498948*r.2 else 16180339887498949*r.2))) = true := by\n  simp only [rows, List.all_append, '+', '.join('part'+str(i)+'_certificate' for i in range(len(chunks)))+', Bool.and_self]\n'
    suffix=suffix[:ebegin]+new_endpoint+suffix[eend:]
    (ROOT/'SubdegreeCIChunkCertificate.lean').write_text(prefix+'\n'.join(blocks)+suffix,encoding='utf8')
    print(json.dumps(dict(contexts=215,scalar_margins=len(rows),chunks=len(chunks),startups=17,integer_margins=len(integers))),flush=True)

if __name__=='__main__':main()

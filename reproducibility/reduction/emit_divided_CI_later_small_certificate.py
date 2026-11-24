"""Complete small later-primitive and actual-startup certificates, kernel reduction."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def main():
    qa=json.loads((ROOT/'audit_divided_CI_later_primitive.json').read_text(encoding='utf8'))
    cut=json.loads((ROOT/'audit_all_padding_primitive_cut.json').read_text(encoding='utf8'))
    rows=qa['small_scalar_certificate'];assert len(rows)==854 and len(qa['small_contexts'])==139
    intervals=qa['rational_root_interval'];den=intervals['denominator'];lo=intervals['lower'];hi=intervals['upper']
    src=(ROOT/'PaddingThreeSmallCertificate.lean').read_text(encoding='utf8')
    begin=src.index('def rows :');end=src.index('\n]\n',begin)+2
    prefix=src[:begin].replace('PaddingThreeSmallCertificate','DividedCILaterSmallCertificate')
    suffix=src[end:].replace('PaddingThreeSmallCertificate','DividedCILaterSmallCertificate')
    suffix=suffix.replace('1618033',str(lo)).replace('1618034',str(hi)).replace('1000000',str(den))
    new_rows='def rows : List (ℤ × ℤ) := [\n'+',\n'.join('  ('+str(a)+', '+str(b)+')' for a,b in rows)+'\n]'
    integers=cut['complete_small_actual_integer_margins']
    assert all(x>=0 for x in integers)
    extra='\ndef actualStartupMargins : List ℤ := ['+', '.join(map(str,integers))+']\n\n'
    extra+='theorem complete_actual_startup_margins : actualStartupMargins.all (fun z => decide (0 ≤ z)) = true := by\n  decide\n\n'
    extra+='#print axioms complete_actual_startup_margins\n\n'
    suffix=suffix.replace('end DividedCILaterSmallCertificate',extra+'end DividedCILaterSmallCertificate')
    (ROOT/'DividedCILaterSmallCertificate.lean').write_text(prefix+new_rows+suffix,encoding='utf8')
    print(json.dumps(dict(complete_small_CI_contexts=139,distinct_later_primitive_scalar_margins=854,
        complete_small_actual_contexts=len(cut['complete_small_actual_contexts']),actual_integer_margins=len(integers))))

if __name__=='__main__':main()

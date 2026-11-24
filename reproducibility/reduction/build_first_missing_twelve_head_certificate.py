"""COMPLETE K=10..12 source-or-strict-head certificate. Critical source sums replay in Lean.
Noncritical classifications and exhaustive host grammar are independently exact-reconstructed;
this is not an end-to-end Lean implementation of the word model or enumerator.
"""
from pathlib import Path
from fractions import Fraction
from math import comb
from collections import Counter
import sys,json,time,hashlib,gzip
ROOT=Path(__file__).resolve().parent
SOURCE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
from probe_binary_first_defect_ordinary_tail import arm
def at(p,n):return p[n] if 0<=n<len(p) else 0
def parts(n,h,lo=1):
    if h==0:
        if n==0:yield []
        return
    for v in range(lo,n//h+1):
        for rest in parts(n-v,h-1,v):yield [v]+rest
def rational_payment(K,d,r,e):
    L=d-e-3
    def t(m):return Fraction(comb(r,m),comb(r+e+m+2,m)) if 0<=m<=r else Fraction(0)
    return t(L)+sum(2**(i-2)*t(L+i) for i in range(2,K-2))-Fraction(e+1,r+1)
def canonical(x):return (json.dumps(x,separators=(',',':'))+'\n').encode()
def write_lean(obligations):
    # Separate modules bound elaborator memory. Every operand remains explicit;
    # one final public aggregate includes every module's complete conjunction.
    modules=[];wholeinputs=[];wholetheorems=[]
    for base in range(0,len(obligations),2500):
        index=base//2500;module='FirstMissingTwelveCriticalPart'+str(index).zfill(2)
        modules.append(module);lines=['import Mathlib','set_option maxHeartbeats 0','set_option maxRecDepth 100000',
            'namespace FirstMissingTwelveCriticalCertificate',''];chunks=[];inputs=[]
        for i in range(base,min(base+2500,len(obligations)),100):
            name='chunk_'+str(i//100);inputname='inputs_'+str(i//100)
            chunks.append(name);inputs.append(inputname);expr=' && '.join(obligations[i:i+100])
            lines+=['private def '+inputname+' : Bool := '+expr,
                'private theorem '+name+' : '+inputname+' = true := by decide','']
        wholeinput='allInputsPart_'+str(index);wholetheorem='allPaymentsPart_'+str(index)
        wholeinputs.append(wholeinput);wholetheorems.append(wholetheorem)
        lines+=['def '+wholeinput+' : Bool := '+' && '.join(inputs),
            'theorem '+wholetheorem+' : '+wholeinput+' = true := by',
            '  simp only ['+', '.join([wholeinput]+chunks+['Bool.and_self'])+']',
            'end FirstMissingTwelveCriticalCertificate']
        (ROOT/(module+'.lean')).write_text('\n'.join(lines)+'\n',encoding='utf8')
    lines=['import '+x for x in modules]+['namespace FirstMissingTwelveCriticalCertificate',
        'theorem complete_all_rank_and_critical_source_payments : ('+' && '.join(wholeinputs)+') = true := by',
        '  simp only ['+', '.join(wholetheorems+['Bool.and_self'])+']',
        'end FirstMissingTwelveCriticalCertificate',
        '#print axioms FirstMissingTwelveCriticalCertificate.complete_all_rank_and_critical_source_payments']
    (ROOT/'FirstMissingTwelveCriticalCertificate.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
def main():
    st=time.monotonic();allct=Counter();byK=[];ranks=[];layers=[];rank_ints=set();head_pairs=set();payments=set()
    streamsha=hashlib.sha256();criticalsha=hashlib.sha256()
    cp=ROOT/'first_missing_twelve_critical_rows.jsonl.gz'
    with cp.open('wb') as raw, gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as zipped:
      for K in [10,11,12]:
        ct=Counter();seen=set();S=(1+(K-2)*(K-1)//2)//2
        for d in range(6,K):
          alpha=K-d;Dmax=min(2*d*(d-3),12*d-25)
          for e in range(d-2):
            for r in range((Dmax-e-2)//2+1):
              D=2*r+2+e;hmax=min(D,3 if d<=6 else (5 if d<=8 else D))
              if hmax<2:continue
              jmax=alpha+D+hmax-r
              row=dict(K=K,alpha=alpha,d=d,e=e,r=r,D=D,hmax=hmax,S=S,jmax=jmax)
              ct['complete_rank_states']+=1
              if jmax-2<=S:
                row['kind']='rank_head';head_pairs.add((jmax-2,S));ct['rank_strict_head_paid']+=1
                ranks.append(row);continue
              p=rational_payment(K,d,r,e)
              row.update(numerator=p.numerator,denominator=p.denominator)
              if p>=0:
                row['kind']='rank_source';rank_ints.update([p.numerator,p.denominator-1]);ct['rank_source_paid']+=1
                ranks.append(row);continue
              row['kind']='owner_complement';ct['unpaid_rank_states']+=1;ranks.append(row)
              hmin=max(2,S+3-alpha-D+r);lct=Counter();lsha=hashlib.sha256()
              for h in range(hmin,hmax+1):
                for ds in parts(D,h):
                  if ds[0]>alpha:continue
                  U=[v+1 for v in ds];seen.add((alpha,tuple(U)));A=arm(alpha,U)[:-2];a=len(A)-1;q=A[::-1]
                  sr=at(q,r)-at(q,r-1);C=at(q,r+1)-2*at(q,r)+at(q,r-1);j=a-r;n=j+1-K
                  ct['complete_owner_rank_inputs']+=1;lct['all']+=1
                  if sr<0 or C<=0:
                    ct['noncritical_owner_edges']+=1;lct['noncritical']+=1
                    state=[K,alpha,U,r,sr,C,'noncritical']
                  else:
                    terms=[at(A,n)]+[at(A,n-i) for i in range(2,K-2)]
                    # The first weight in terms[1:] is one, followed by 2,4,... .
                    pay=terms[0]+sum(2**i*v for i,v in enumerate(terms[1:]))
                    assert pay>=C,(K,alpha,U,r,C,pay)
                    state=[K,alpha,U,r,sr,C,'source_paid',j,n,terms,pay]
                    encoded=canonical(state);zipped.write(encoded);criticalsha.update(encoded)
                    payments.add((C,tuple(terms)));ct['positive_curvature_owner_edges']+=1
                    ct['direct_owner_source_paid']+=1;lct['critical']+=1
                  encoded=canonical(state);streamsha.update(encoded);lsha.update(encoded)
              layers.append(dict(K=K,alpha=alpha,D=D,r=r,e=e,hmin=hmin,hmax=hmax,
                counts=dict(lct),all_state_sha256=lsha.hexdigest()))
        ct['distinct_canonical_owners']=len(seen);allct.update(ct);byK.append(dict(K=K,S=S,counts=dict(ct)))
        print(json.dumps(dict(K=K,counts=dict(ct),seconds=time.monotonic()-st)),flush=True)
    obligations=[]
    for v in sorted(rank_ints):obligations.append(f'decide ((0 : Int) ≤ {v})')
    for j,S in sorted(head_pairs):obligations.append(f'decide (({j} : Int) ≤ {S})')
    for C,terms in sorted(payments):
        expression=str(terms[0])+'+'+'+'.join(str(2**i)+'*'+str(v) for i,v in enumerate(terms[1:]))
        obligations.append(f'decide (({C} : Int) ≤ {expression})')
    data=dict(status='COMPLETE_FIRST_MISSING_TEN_THROUGH_TWELVE_SOURCE_OR_HEAD_PROOF_INPUTS',
        counts=dict(allct),by_K=byK,ALL_rank_states=ranks,ALL_complement_layers=layers,
        rational_integer_margins=sorted(rank_ints),head_rank_pairs=[list(x) for x in sorted(head_pairs)],
        critical_source_payments=[[C,list(T)] for C,T in sorted(payments)],
        kernel_obligations=len(obligations),ALL_owner_state_sha256=streamsha.hexdigest(),
        critical_stream_sha256=criticalsha.hexdigest(),critical_compressed_sha256=hashlib.sha256(cp.read_bytes()).hexdigest(),
        scope='COMPLETE K10..12rank/head/source reductions and ALL1.8Mowner-rank classifications. ALLcritical source SUM inequalities replayed in kernel;noncritical curvature decisions/exhaustive grammar independently exact,NOTendtoendLean.',
        seconds=time.monotonic()-st)
    (ROOT/'first_missing_twelve_head_certificate_data.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    write_lean(obligations)
    print(json.dumps(dict(status=data['status'],counts=dict(allct),unique_source_payments=len(payments),
        rank_integer_margins=len(rank_ints),head_pairs=len(head_pairs),kernel_obligations=len(obligations),chunks=(len(obligations)+99)//100,
        critical_compressed_bytes=cp.stat().st_size,seconds=time.monotonic()-st)),flush=True)
if __name__=='__main__':
    if '--lean-only' in sys.argv:
        data=json.loads((ROOT/'first_missing_twelve_head_certificate_data.json').read_text(encoding='utf8'))
        obligations=[f'decide ((0 : Int) ≤ {v})' for v in data['rational_integer_margins']]
        obligations += [f'decide (({j} : Int) ≤ {S})' for j,S in data['head_rank_pairs']]
        for C,terms in data['critical_source_payments']:
            expression=str(terms[0])+'+'+'+'.join(str(2**i)+'*'+str(v) for i,v in enumerate(terms[1:]))
            obligations.append(f'decide (({C} : Int) ≤ {expression})')
        assert len(obligations)==data['kernel_obligations'];write_lean(obligations)
        print('Re-emitted ALL75372 obligations with explicit private input definitions and ONE public aggregate.')
    else:main()

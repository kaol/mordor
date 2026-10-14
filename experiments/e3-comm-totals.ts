// Mordor — commutation-total validation harness (round 20 revalidation).
//
// Structure-aware enumeration of commuting polar pairs per routing class,
// WITHOUT realizability filters. Expected totals (must match exactly):
//   000.002 STAR  4,717,955   001.021 CHN  2,654,872
//   001.001 CHN   3,056,151   002.010 SGL  9,361,547
//   002.102 SGL   4,578,444 (RB[0]!=0 path, h4 relief at k=0,1)
//   012.021 ID   10,870,821 (factored: for ra=id the per-column conditions
//                             decouple; total = s0 * s12)
//
// Commutation per source column k:
//   comp[A[rb[k]]][B[k]] === comp[B[ra[k]]][A[k]]
//   && (ra[rb[k]] === rb[ra[k]] || common triple is bound-only (H4))
// The H4 clause is exact: with differing target columns, middle elements of
// different columns are incomparable, so agreement forces bound-only values,
// and then the position triples agree too.

async function main(){
const T=[],tk=new Map();
for(let a=0;a<5;a++)for(let b=a;b<5;b++)for(let c=b;c<5;c++){tk.set(a*100+b*10+c,T.length);T.push([a,b,c]);}
const ap=(m,p)=>p===0?0:p===4?4:T[m][p-1];
const comp=[];for(let u=0;u<35;u++){comp[u]=new Uint8Array(35);for(let v=0;v<35;v++){let k=0;for(let p=1;p<4;p++)k=k*10+ap(u,ap(v,p));comp[u][v]=tk.get(k);}}
let idok=1;for(let v=0;v<35;v++)if(comp[20][v]!==v||comp[v][20]!==v)idok=0; // id=20 commutes with all
const h4b=new Uint8Array(35);for(const i of[0,4,14,34])h4b[i]=1;
const CFG=[
["000.002",[0,0,0],[0,0,2],0,4717955],
["001.021",[0,0,1],[0,2,1],1,2654872],
["001.001",[0,0,1],[0,0,1],1,3056151],
["002.010",[0,0,2],[0,1,0],2,9361547],
["002.102",[0,0,2],[1,0,2],2,4578444]];
const out=[];
for(const cf of CFG){const RA=cf[1],RB=cf[2],ST=cf[3];
const r0=(RA[RB[0]]===RB[RA[0]])?1:0,r1=(RA[RB[1]]===RB[RA[1]])?1:0,r2=(RA[RB[2]]===RB[RA[2]])?1:0;
let n=0;
for(let a0=0;a0<35;a0++)for(let a1=0;a1<35;a1++)for(let a2=0;a2<35;a2++){
const ab0=RB[0]===0?a0:RB[0]===1?a1:a2,ab1=RB[1]===0?a0:RB[1]===1?a1:a2,ab2=RB[2]===0?a0:RB[2]===1?a1:a2;
for(let b0=0;b0<35;b0++){const c0=comp[ab0][b0];if(c0!==comp[b0][a0]||(!r0&&!h4b[c0]))continue;
for(let b1=0;b1<35;b1++){const vm1=ST===3?b1:b0,c1=comp[ab1][b1];if(c1!==comp[vm1][a1]||(!r1&&!h4b[c1]))continue;
for(let b2=0;b2<35;b2++){const vm2=ST===0?b0:ST===1?b1:b2,c2=comp[ab2][b2];if(c2!==comp[vm2][a2]||(!r2&&!h4b[c2]))continue;n++;}}}}
out.push({cls:cf[0],got:n,exp:cf[4],ok:n===cf[4]});}
// ID class 012.021, factored
{let s0=0,s12=0;
for(let a0=0;a0<35;a0++)for(let b0=0;b0<35;b0++){const c=comp[a0][b0];if(c===comp[b0][a0])s0++;}
for(let a1=0;a1<35;a1++)for(let a2=0;a2<35;a2++)
for(let b1=0;b1<35;b1++){const c1=comp[a2][b1];if(c1!==comp[b1][a1])continue;
for(let b2=0;b2<35;b2++){if(comp[a1][b2]===comp[b2][a2])s12++;}}
const g=s0*s12;out.push({cls:"012.021",got:g,exp:10870821,ok:g===10870821});}
return {idok,all:out.every(o=>o.ok),out};}

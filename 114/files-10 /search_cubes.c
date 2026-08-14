/* search_cubes.c -- search for integer solutions of x^3 + y^3 + z^3 = k
 *
 * Heath-Brown / Booker divisor method.  Assume |x| > |y| > |z| and set d = |x+y|.
 * Then d > 0 and (x,y,z) is a solution iff
 *      (i)  z^3 == k  (mod d)
 *      (ii) Delta(d,z) := 3d(4|k - z^3| - d^3)  is a perfect square,
 * from which x,y = (sigma*d +- sqrt(Delta)/(3d)) / 2.
 *
 * Requires k == +-3 (mod 9) (holds for k = 114, 3, 30, 33, 39, 42, 165, ...).
 * Writing k == 3*eps (mod 9) this forces x == y == z == eps (mod 3), so 3 does
 * not divide d, sgn(z) = eps * (d|3), sgn(x+y) = -sgn(z), and |z| > d/alpha
 * with alpha = 2^(1/3) - 1.
 *
 * Finds every solution with min(|x|,|y|,|z|) <= zmax and |x+y| in [d0,d1],
 * except the two degenerate families (x = -y, and y = z) which are handled
 * separately -- see degenerate.py.
 *
 * Build: gcc -O3 -march=native -o search_cubes search_cubes.c -lm
 * Run:   ./search_cubes -k 114 -d0 1 -d1 1000000 -z 1e15
 *
 * SCOPE: self-contained and verifiable, but NOT competitive with the tuned
 * Booker-Sutherland implementation (github.com/AndrewVSutherland/SumsOfThreeCubes).
 * Missing: cubic-reciprocity constraints mod 81k (a further 2-4x), incremental
 * CRT enumeration, and d generated multiplicatively from admissible primes
 * (this code factors d by sieving, which caps d1 at roughly 10^13).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

typedef unsigned __int128 u128;
typedef __int128          i128;
typedef uint64_t          u64;
typedef uint32_t          u32;
typedef int64_t           i64;

/* ============================================================ 256-bit ints */
typedef struct { u64 v[4]; } u256;

static inline int u256_cmp(u256 a,u256 b){ for(int i=3;i>=0;i--) if(a.v[i]!=b.v[i]) return a.v[i]<b.v[i]?-1:1; return 0; }
static inline u256 u256_sub(u256 a,u256 b){ u256 r; u64 br=0; for(int i=0;i<4;i++){ u128 t=(u128)a.v[i]-b.v[i]-br; r.v[i]=(u64)t; br=(t>>127)&1; } return r; }
static inline u256 u256_add_u64(u256 a,u64 b){ u128 c=b; for(int i=0;i<4;i++){ u128 s=(u128)a.v[i]+c; a.v[i]=(u64)s; c=s>>64; if(!c) break; } return a; }
static inline u256 u256_sub_u64(u256 a,u64 b){ u128 br=b; for(int i=0;i<4;i++){ u128 t=(u128)a.v[i]-(u64)br-(u64)(br>>64); a.v[i]=(u64)t; br=(t>>127)&1; if(!br) break; } return a; }
static inline u256 u256_shl2(u256 a){ u256 r; u64 c=0; for(int i=0;i<4;i++){ r.v[i]=(a.v[i]<<2)|c; c=a.v[i]>>62; } return r; }

static u256 mul_128x128(u128 a,u128 b){
    u64 a0=(u64)a,a1=(u64)(a>>64),b0=(u64)b,b1=(u64)(b>>64);
    u128 p00=(u128)a0*b0,p01=(u128)a0*b1,p10=(u128)a1*b0,p11=(u128)a1*b1;
    u256 r;
    r.v[0]=(u64)p00;
    u128 mid=(p00>>64)+(u64)p01+(u64)p10;      r.v[1]=(u64)mid;
    u128 hi =(mid>>64)+(p01>>64)+(p10>>64)+(u64)p11; r.v[2]=(u64)hi;
    r.v[3]=(u64)((hi>>64)+(p11>>64));
    return r;
}
static u256 mul_256x64(u256 a,u64 f){
    u256 r={{0,0,0,0}}; u128 c=0;
    for(int i=0;i<4;i++){ u128 t=(u128)a.v[i]*f+c; r.v[i]=(u64)t; c=t>>64; }
    return r;                                   /* caller guarantees no overflow */
}
static int u256_is_square(u256 a,u128 *root){
    if(a.v[3]>>58) return 0;                    /* >= 2^250: outside supported range */
    u128 lo=0,hi=(u128)1<<126,r=0;
    while(lo<hi){ u128 mid=lo+((hi-lo)>>1); u256 sq=mul_128x128(mid,mid);
                  if(u256_cmp(sq,a)<=0){ r=mid; lo=mid+1; } else hi=mid; }
    if(u256_cmp(mul_128x128(r,r),a)==0){ *root=r; return 1; }
    return 0;
}

/* ============================================================ modular util */
static inline u64 mulmod(u64 a,u64 b,u64 m){ return (u64)((u128)a*b%m); }
static u64 powmod(u64 a,u64 e,u64 m){ u64 r=1;a%=m; while(e){ if(e&1) r=mulmod(r,a,m); a=mulmod(a,a,m); e>>=1;} return r; }
static u64 inv_mod(u64 a,u64 m){ i64 t=0,nt=1; u64 r=m,nr=a%m;
    while(nr){ u64 q=r/nr; i64 tmp=t-(i64)q*nt; t=nt; nt=tmp; u64 tr=r-q*nr; r=nr; nr=tr; }
    if(t<0) t+=(i64)m;
    return (u64)t; }

/* one cube root of a mod p, p prime == 1 (mod 3), a a cubic residue */
static int cube_root_p1mod3(u64 a,u64 p,u64 *out){
    u64 s=0,t=p-1; while(t%3==0){ t/=3; s++; }
    if(powmod(a,(p-1)/3,p)!=1) return 0;
    u64 c=0;
    for(u64 g=2;g<p;g++){ if(powmod(g,(p-1)/3,p)!=1){ c=powmod(g,t,p); break; } }
    if(!c) return 0;
    u64 ord=1; for(u64 i=0;i<s;i++) ord*=3;
    u64 w=powmod(c,ord/3,p);                     /* exact order 3 */
    u64 A=powmod(a,t,p),e=0,p3=1,cinv=inv_mod(c,p);
    for(u64 i=0;i<s;i++){
        u64 x=mulmod(A,powmod(cinv,e,p),p);
        u64 ex=1; for(u64 j=0;j<s-1-i;j++) ex*=3;
        u64 h=powmod(x,ex,p),cur=1,dig=3;
        for(u64 dd=0;dd<3;dd++){ if(cur==h){ dig=dd; break; } cur=mulmod(cur,w,p); }
        if(dig==3) return 0;
        e+=dig*p3; p3*=3;
    }
    if(e%3) return 0;
    u64 lam=1; if((1+t)%3) lam=2;
    if((1+lam*t)%3) return 0;
    u64 m=(1+lam*t)/3;
    u64 n=(((ord-(e%ord))%ord)*lam/3)%ord;
    *out=mulmod(powmod(a,m,p),powmod(c,n,p),p);
    return 1;
}
static int cube_roots_mod_p(u64 k,u64 p,u64 *r){
    u64 a=k%p;
    if(p==2){ r[0]=a; return 1; }
    if(p==3){ r[0]=a%3; return 1; }
    if(a==0){ r[0]=0; return 1; }
    if(p%3==2){ r[0]=powmod(a,(2*p-1)/3,p); return 1; }
    u64 x; if(!cube_root_p1mod3(a,p,&x)) return 0;
    u64 w=0; for(u64 g=2;g<p;g++){ u64 c=powmod(g,(p-1)/3,p); if(c!=1){ w=c; break; } }
    r[0]=x; r[1]=mulmod(x,w,p); r[2]=mulmod(x,mulmod(w,w,p),p);
    return 3;
}
#define MAXR 2048
static int cube_roots_mod_pe(u64 k,u64 p,int e,u64 *buf){
    if(p>3 && k%p!=0){
        u64 base[3]; int nb=cube_roots_mod_p(k,p,base);
        if(!nb) return 0;
        for(int i=0;i<nb;i++) buf[i]=base[i];
        u64 pe=p;
        for(int i=1;i<e;i++){
            u64 npe=pe*p;
            for(int j=0;j<nb;j++){
                u64 z=buf[j]%npe;
                u64 f=(mulmod(mulmod(z,z,npe),z,npe)+npe-k%npe)%npe;
                u64 dv=inv_mod(mulmod(3,mulmod(z,z,npe),npe),npe);
                buf[j]=(z+npe-mulmod(f,dv,npe))%npe;
            }
            pe=npe;
        }
        return nb;
    }
    u64 pe=1; int n=1; buf[0]=0;
    static u64 tmp[MAXR];
    for(int i=0;i<e;i++){
        u64 npe=pe*p; int m=0;
        for(int j=0;j<n;j++) for(u64 c=0;c<p;c++){
            u64 z=(buf[j]+c*pe)%npe;
            if(mulmod(mulmod(z,z,npe),z,npe)==k%npe){ if(m>=MAXR) return -1; tmp[m++]=z; }
        }
        if(!m) return 0;
        memcpy(buf,tmp,m*sizeof(u64)); n=m; pe=npe;
    }
    return n;
}

/* ============================================== auxiliary sieve primes */
static const u64 AUXP[]={5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,
                         83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,
                         167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251};
#define NAUX (int)(sizeof(AUXP)/sizeof(AUXP[0]))
/* Sd[i][dm][sg] = residues za (mod p) for which Delta(d,za) is a QR mod p,
   depending on d only through dm = d mod p and on sg = (sgn z < 0).       */
static unsigned char *Sres[NAUX][2];   /* [i][sg] -> flat array p*p of residues */
static unsigned char *Sbit[NAUX][2];   /* [i][sg] -> flat p*p membership bitmap */
static int           *Scnt[NAUX][2];   /* [i][sg] -> counts per dm            */
static u64 K; static int EPS;

static void build_aux(void){
    for(int i=0;i<NAUX;i++){
        u64 p=AUXP[i];
        if(K%p==0){ for(int sg=0;sg<2;sg++){ Sres[i][sg]=NULL; Sbit[i][sg]=NULL; Scnt[i][sg]=NULL; } continue; }
        unsigned char *qr=malloc(p),*cb=malloc(p);
        memset(qr,0,p);
        for(u64 v=0;v<p;v++) cb[v]=(unsigned char)mulmod(mulmod(v,v,p),v,p);
        qr[0]=1; for(u64 v=1;v<p;v++) qr[mulmod(v,v,p)]=1;
        for(int sg=0;sg<2;sg++){
            Sres[i][sg]=malloc(p*p); Sbit[i][sg]=malloc(p*p); Scnt[i][sg]=malloc(sizeof(int)*p);
            memset(Sbit[i][sg],0,p*p);
            u64 tk = (sg==0)? (K%p) : (p-K%p)%p;          /* subtract sgn*k */
            for(u64 dm=0;dm<p;dm++){
                int c=0;
                if(dm==0){ Scnt[i][sg][dm]=0; continue; }
                u64 d3=mulmod(mulmod(dm,dm,p),dm,p), f=mulmod(3,dm,p);
                for(u64 r=0;r<p;r++){
                    u64 v=(cb[r]+p-tk)%p;
                    v=mulmod(4%p,v,p);
                    v=(v+p-d3)%p;
                    v=mulmod(f,v,p);
                    if(qr[v]){ Sres[i][sg][dm*p+c]=(unsigned char)r; Sbit[i][sg][dm*p+r]=1; c++; }
                }
                Scnt[i][sg][dm]=c;
            }
        }
        free(qr); free(cb);
    }
}

/* ================================================== segmented factorisation */
static u64 *sprimes; static int nsprimes;
static void build_primes(u64 lim){
    if(lim<2) lim=2;
    char *sv=calloc(lim+1,1);
    sprimes=malloc(sizeof(u64)*(size_t)(1.3*lim/log((double)lim>2?(double)lim:2.0)+100));
    nsprimes=0;
    for(u64 i=2;i<=lim;i++) if(!sv[i]){ sprimes[nsprimes++]=i; for(u64 j=i*i;j<=lim;j+=i) sv[j]=1; }
    free(sv);
}

/* ============================================================= exact check */
static FILE *OUT; static u64 g_tested=0,g_cands=0,g_found=0;
static void print_i128(char*b,i128 x){ char t[64]; int n=0; int neg=x<0; u128 a=neg?(u128)(-x):(u128)x;
    do{ t[n++]='0'+(int)(a%10); a/=10; }while(a); int m=0; if(neg) b[m++]='-';
    while(n) b[m++]=t[--n];
    b[m]=0; }

static int exact_check(u64 d,u64 za,int sgn){
    u128 za2=(u128)za*za;
    u256 z3=mul_128x128(za2,(u128)za);
    u256 N = (sgn>0)? u256_sub_u64(z3,K) : u256_add_u64(z3,K);   /* |k - z^3| */
    u256 four=u256_shl2(N);
    u256 d3=mul_128x128((u128)d*d,(u128)d);
    if(u256_cmp(four,d3)<=0) return 0;
    u256 diff=u256_sub(four,d3);
    u256 D=mul_256x64(diff,3*d);
    g_tested++;
    u128 root;
    if(!u256_is_square(D,&root)) return 0;
    if(root%(3*(u128)d)) return 0;
    u128 sq=root/(3*(u128)d);
    i128 dd=(i128)(-sgn)*(i128)d;                 /* sigma*d, sigma = -sgn(z) */
    if(((dd+(i128)sq)&1)!=0) return 0;
    i128 x=(dd+(i128)sq)/2, y=(dd-(i128)sq)/2, z=(i128)sgn*(i128)za;
    /* exact verification x^3+y^3+z^3 == k, done in u256 with signs split */
    u256 P[3]; int neg[3]; i128 vv[3]={x,y,z};
    for(int i=0;i<3;i++){ i128 t=vv[i]; neg[i]=t<0; u128 a=neg[i]?(u128)(-t):(u128)t;
        P[i]=mul_128x128((u128)((u128)a*a),(u128)a); }
    u256 pos={{0,0,0,0}},ng={{0,0,0,0}};
    for(int i=0;i<3;i++){ u256*t=neg[i]?&ng:&pos; u128 c=0;
        for(int j=0;j<4;j++){ u128 s=(u128)t->v[j]+P[i].v[j]+c; t->v[j]=(u64)s; c=s>>64; } }
    u256 chk=u256_sub(pos,ng);
    u256 kk={{K,0,0,0}};
    if(u256_cmp(chk,kk)!=0) return 0;
    char bx[64],by[64],bz[64];
    print_i128(bx,x); print_i128(by,y); print_i128(bz,z);
    fprintf(OUT,"SOLUTION k=%llu x=%s y=%s z=%s d=%llu\n",(unsigned long long)K,bx,by,bz,(unsigned long long)d);
    fflush(OUT); g_found++;
    return 1;
}

/* ==================================================================== main */
int main(int argc,char**argv){
    u64 d0=1,d1=1000000; long double zf=1e12L; const char*outf=NULL; K=114;
    for(int i=1;i<argc;i++){
        if(!strcmp(argv[i],"-k")) K=strtoull(argv[++i],0,10);
        else if(!strcmp(argv[i],"-d0")) d0=(u64)strtold(argv[++i],0);
        else if(!strcmp(argv[i],"-d1")) d1=(u64)strtold(argv[++i],0);
        else if(!strcmp(argv[i],"-z"))  zf=strtold(argv[++i],0);
        else if(!strcmp(argv[i],"-o"))  outf=argv[++i];
        else { fprintf(stderr,"usage: %s -k K -d0 D0 -d1 D1 -z ZMAX [-o FILE]\n",argv[0]); return 1; }
    }
    if(zf>4e18L){ fprintf(stderr,"zmax capped to 4e18\n"); zf=4e18L; }
    u64 zmax=(u64)zf;
    int km9=(int)(K%9);
    if(km9==3) EPS=1; else if(km9==6) EPS=-1;
    else { fprintf(stderr,"this program needs k == +-3 (mod 9)\n"); return 1; }
    OUT=outf?fopen(outf,"a"):stdout;
    if(d0<1) d0=1;
    build_primes((u64)(sqrtl((long double)d1)+2));
    build_aux();
    double alpha=0.2599210498948732, kcrt=cbrt((double)K);

    const u64 SEG=1u<<16;
    u64  *cof=malloc(sizeof(u64)*SEG);
    u32  *fac=malloc(sizeof(u32)*SEG*48);
    unsigned char *nf=malloc(SEG);

    for(u64 base=d0;base<=d1;base+=SEG){
        u64 hi=base+SEG-1; if(hi>d1) hi=d1;
        u64 n=hi-base+1;
        for(u64 i=0;i<n;i++){ cof[i]=base+i; nf[i]=0; }
        for(int pi=0;pi<nsprimes;pi++){
            u64 p=sprimes[pi]; if(p*p>hi) break;
            u64 st=((base+p-1)/p)*p;
            for(u64 m=st;m<=hi;m+=p){ u64 i=m-base;
                while(cof[i]%p==0){ cof[i]/=p; if(nf[i]<48) fac[i*48+nf[i]++]=(u32)p; } }
        }
        for(u64 i=0;i<n;i++){
            u64 d=base+i;
            if(d%3==0||d==0) continue;
            /* --- cube roots of k mod d --------------------------------- */
            static u64 res[MAXR]; int nres=1; res[0]=0; u64 mod=1; int dead=0;
            u64 pl[64]; int el[64],np=0;
            for(int j=0;j<nf[i];j++){ u64 p=fac[i*48+j];
                if(np&&pl[np-1]==p) el[np-1]++; else { pl[np]=p; el[np]=1; np++; } }
            if(cof[i]>1){ pl[np]=cof[i]; el[np]=1; np++; }
            for(int j=0;j<np&&!dead;j++){
                u64 q=1; for(int t=0;t<el[j];t++) q*=pl[j];
                static u64 rb[MAXR];
                int nr=cube_roots_mod_pe(K,pl[j],el[j],rb);
                if(nr<=0){ dead=1; break; }
                if((long long)nres*nr>MAXR){ dead=1; break; }
                static u64 nw[MAXR]; int c=0; u64 iv=inv_mod(mod%q,q);
                for(int a=0;a<nres;a++) for(int b=0;b<nr;b++){
                    u64 df=(rb[b]+q-res[a]%q)%q;
                    nw[c++]=res[a]+mod*mulmod(df,iv,q);
                }
                memcpy(res,nw,c*sizeof(u64)); nres=c; mod*=q;
            }
            if(dead||!nres) continue;
            /* --- sign, mod-3 class, scan window ------------------------ */
            int sgn=EPS*((d%3==1)?1:-1);
            int sg=(sgn>0)?0:1;
            u64 M0=3*mod, iv3=inv_mod(mod%3,3), e3=(EPS>0)?1:2;
            static u64 R0[MAXR]; int nR0=0;
            for(int a=0;a<nres;a++){
                u64 df=(e3+3-res[a]%3)%3;
                u64 r=res[a]+mod*mulmod(df,iv3,3);
                R0[nR0++]= (sgn>0)? r%M0 : (M0-r%M0)%M0;      /* residue of |z| */
            }
            u64 zlo=(u64)(d/alpha)+1; if(zlo<(u64)kcrt+1) zlo=(u64)kcrt+1;
            if(zlo>zmax) continue;
            /* --- pick CRT primes (most restrictive first) -------------- */
            int ord[NAUX],no=0;
            for(int j=0;j<NAUX;j++){ u64 p=AUXP[j];
                if(!Sres[j][sg] || d%p==0) continue;
                ord[no++]=j; }
            for(int a=0;a<no;a++) for(int b=a+1;b<no;b++){
                int ia=ord[a],ib=ord[b];
                double ra=(double)Scnt[ia][sg][d%AUXP[ia]]/AUXP[ia];
                double rb2=(double)Scnt[ib][sg][d%AUXP[ib]]/AUXP[ib];
                if(rb2<ra){ ord[a]=ib; ord[b]=ia; }
            }
            int crtn=0; u64 M=M0; double combos=nR0;
            while(crtn<no && combos<(1<<20)){
                int j=ord[crtn]; u64 p=AUXP[j];
                if(!Scnt[j][sg][d%p]) { crtn++; combos=0; break; }   /* empty: no z at all */
                if(M> zmax/(8*p)) break;
                M*=p; combos*=Scnt[j][sg][d%p]; crtn++;
            }
            if(combos==0) continue;
            int chk[12],nchk=0;
            for(int j=crtn;j<no&&nchk<10;j++) chk[nchk++]=ord[j];
            /* --- enumerate the CRT product and scan -------------------- */
            int idx[32];
            for(int a=0;a<nR0;a++){
                for(int j=0;j<crtn;j++) idx[j]=0;
                for(;;){
                    u64 r=R0[a],mm=M0;
                    for(int j=0;j<crtn;j++){
                        int pj=ord[j]; u64 p=AUXP[pj];
                        u64 rr=Sres[pj][sg][(d%p)*p+idx[j]];
                        u64 df=(rr+p-r%p)%p;
                        r+=mm*mulmod(df,inv_mod(mm%p,p),p);
                        mm*=p;
                    }
                    u64 start=r%mm;
                    if(start<zlo) start+=((zlo-start+mm-1)/mm)*mm;
                    for(u64 za=start;za<=zmax;za+=mm){
                        g_cands++;
                        int pass=1;
                        for(int j=0;j<nchk;j++){ int pj=chk[j]; u64 p=AUXP[pj];
                            if(!Sbit[pj][sg][(d%p)*p+za%p]){ pass=0; break; } }
                        if(pass) exact_check(d,za,sgn);
                    }
                    int j=crtn-1;
                    for(;j>=0;j--){ idx[j]++; if(idx[j]<Scnt[ord[j]][sg][d%AUXP[ord[j]]]) break; idx[j]=0; }
                    if(j<0) break;
                }
            }
        }
    }
    fprintf(stderr,"done k=%llu d=[%llu,%llu] zmax=%llu cands=%llu exact=%llu found=%llu\n",
        (unsigned long long)K,(unsigned long long)d0,(unsigned long long)d1,(unsigned long long)zmax,
        (unsigned long long)g_cands,(unsigned long long)g_tested,(unsigned long long)g_found);
    return 0;
}

//
//  PoS.c
//  PoS
//
//  Created by Shaft on 01/03/2015.
//  Copyright (c) 2015 Metalogic. All rights reserved.
//

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>

#define treesz (1ULL<<(treepwr))
#define dopesz (1ULL<<(dopepwr))
#define dopebyts (dopesz*sizeof(node))
#define dopes (1ULL<<(treepwr-dopepwr))
#define treerow(nx) ((nx)>> dopepwr)
#define tree(nx) treedope[treerow(nx)][(nx)&(dopesz-1)]
#define hopmsk (treesz -1)
#define hopmod 65537
#define hsz 64
#define hwds 8
#define vers 32
#define hops (1<<(dopepwr-15)) // average 2-3 bufs
#define bufs 2
#define errv (0xffffffffffffffff)
#define kd1 7
#define kd2 256
#define kd3 3125
#define kd4 28657 // Fibonacci Prime
#define norow 999999

typedef unsigned char uchar;
typedef unsigned int uint;
typedef uint64_t ulint;
const uchar id[]="2201195222011952220119522201195222011952220119522201195222011952"; // 512 bits
//const char Proof[]="/work/users/bshaft/PROOF\0", Roots[]="/work/users/bshaft/ROOTS\0";
const char Proof[]="/tmp/PROOF\0", Roots[]="/tmp/ROOTS\0";
uchar num[hsz], bcnt= 0;
int Pfd;
uint treepwr,dopepwr;
typedef struct {uchar chsh[hsz], thsh[hsz];} node;
typedef struct {ulint ptreex; uchar pphsh[hsz], pchsh[hsz], pthsh[hsz];} prnode;
unsigned char rhash[hsz+hsz], hashbuf[hsz*3];
node **treedope, **treebufs, *tbuf;
ulint dds=0, toffs= 0, tlim= 0, bufmap[3];
/*
 BLAKE2 reference source code package - reference C implementations
 
 Written in 2012 by Samuel Neves <sneves@dei.uc.pt>
 
 To the extent possible under law, the author(s) have dedicated all copyright
 and related and neighboring rights to this software to the public domain
 worldwide. This software is distributed without any warranty.
 
 You should have received a copy of the CC0 Public Domain Dedication along with
 this software. If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
 */

#include <stdint.h>

#include "blake/ref/blake2.h"
#include "blake/ref/blake2-impl.h"

static const uint64_t blake2b_IV[8] =
{
   0x6a09e667f3bcc908ULL, 0xbb67ae8584caa73bULL,
   0x3c6ef372fe94f82bULL, 0xa54ff53a5f1d36f1ULL,
   0x510e527fade682d1ULL, 0x9b05688c2b3e6c1fULL,
   0x1f83d9abfb41bd6bULL, 0x5be0cd19137e2179ULL
};

static const uint8_t blake2b_sigma[12][16] =
{
   {  0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15 } ,
   { 14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3 } ,
   { 11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4 } ,
   {  7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8 } ,
   {  9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13 } ,
   {  2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9 } ,
   { 12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11 } ,
   { 13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10 } ,
   {  6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5 } ,
   { 10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13 , 0 } ,
   {  0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15 } ,
   { 14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3 }
};


static inline int blake2b_set_lastnode( blake2b_state *S )
{
   S->f[1] = ~0ULL;
   return 0;
}

/* Some helper functions, not necessarily useful */
static inline int blake2b_set_lastblock( blake2b_state *S )
{
   if( S->last_node ) blake2b_set_lastnode( S );
   
   S->f[0] = ~0ULL;
   return 0;
}

static inline int blake2b_increment_counter( blake2b_state *S, const uint64_t inc )
{
   S->t[0] += inc;
   S->t[1] += ( S->t[0] < inc );
   return 0;
}

static inline int blake2b_init0( blake2b_state *S )
{
   memset( S, 0, sizeof( blake2b_state ) );
   
   for( int i = 0; i < 8; ++i ) S->h[i] = blake2b_IV[i];
   
   return 0;
}

/* init xors IV with input parameter block */
int blake2b_init_param( blake2b_state *S, const blake2b_param *P )
{
   blake2b_init0( S );
   uint8_t *p = ( uint8_t * )( P );
   
   /* IV XOR ParamBlock */
   for( size_t i = 0; i < 8; ++i )
      S->h[i] ^= load64( p + sizeof( S->h[i] ) * i );
   
   return 0;
}



int blake2b_init( blake2b_state *S, const uint8_t outlen )
{
   blake2b_param P[1];
   
   if ( ( !outlen ) || ( outlen > BLAKE2B_OUTBYTES ) ) return -1;
   
   P->digest_length = outlen;
   P->key_length    = 0;
   P->fanout        = 1;
   P->depth         = 1;
   store32( &P->leaf_length, 0 );
   store64( &P->node_offset, 0 );
   P->node_depth    = 0;
   P->inner_length  = 0;
   memset( P->reserved, 0, sizeof( P->reserved ) );
   memset( P->salt,     0, sizeof( P->salt ) );
   memset( P->personal, 0, sizeof( P->personal ) );
   return blake2b_init_param( S, P );
}


int blake2b_init_key( blake2b_state *S, const uint8_t outlen, const void *key, const uint8_t keylen )
{
   blake2b_param P[1];
   
   if ( ( !outlen ) || ( outlen > BLAKE2B_OUTBYTES ) ) return -1;
   
   if ( !key || !keylen || keylen > BLAKE2B_KEYBYTES ) return -1;
   
   P->digest_length = outlen;
   P->key_length    = keylen;
   P->fanout        = 1;
   P->depth         = 1;
   store32( &P->leaf_length, 0 );
   store64( &P->node_offset, 0 );
   P->node_depth    = 0;
   P->inner_length  = 0;
   memset( P->reserved, 0, sizeof( P->reserved ) );
   memset( P->salt,     0, sizeof( P->salt ) );
   memset( P->personal, 0, sizeof( P->personal ) );
   
   if( blake2b_init_param( S, P ) < 0 ) return -1;
   
   {
      uint8_t block[BLAKE2B_BLOCKBYTES];
      memset( block, 0, BLAKE2B_BLOCKBYTES );
      memcpy( block, key, keylen );
      blake2b_update( S, block, BLAKE2B_BLOCKBYTES );
      secure_zero_memory( block, BLAKE2B_BLOCKBYTES ); /* Burn the key from stack */
   }
   return 0;
}

static int blake2b_compress( blake2b_state *S, const uint8_t block[BLAKE2B_BLOCKBYTES] )
{
   uint64_t m[16];
   uint64_t v[16];
   int i;
   
   for( i = 0; i < 16; ++i )
      m[i] = load64( block + i * sizeof( m[i] ) );
   
   for( i = 0; i < 8; ++i )
      v[i] = S->h[i];
   
   v[ 8] = blake2b_IV[0];
   v[ 9] = blake2b_IV[1];
   v[10] = blake2b_IV[2];
   v[11] = blake2b_IV[3];
   v[12] = S->t[0] ^ blake2b_IV[4];
   v[13] = S->t[1] ^ blake2b_IV[5];
   v[14] = S->f[0] ^ blake2b_IV[6];
   v[15] = S->f[1] ^ blake2b_IV[7];
#define G(r,i,a,b,c,d) \
do { \
a = a + b + m[blake2b_sigma[r][2*i+0]]; \
d = rotr64(d ^ a, 32); \
c = c + d; \
b = rotr64(b ^ c, 24); \
a = a + b + m[blake2b_sigma[r][2*i+1]]; \
d = rotr64(d ^ a, 16); \
c = c + d; \
b = rotr64(b ^ c, 63); \
} while(0)
#define ROUND(r)  \
do { \
G(r,0,v[ 0],v[ 4],v[ 8],v[12]); \
G(r,1,v[ 1],v[ 5],v[ 9],v[13]); \
G(r,2,v[ 2],v[ 6],v[10],v[14]); \
G(r,3,v[ 3],v[ 7],v[11],v[15]); \
G(r,4,v[ 0],v[ 5],v[10],v[15]); \
G(r,5,v[ 1],v[ 6],v[11],v[12]); \
G(r,6,v[ 2],v[ 7],v[ 8],v[13]); \
G(r,7,v[ 3],v[ 4],v[ 9],v[14]); \
} while(0)
   ROUND( 0 );
   ROUND( 1 );
   ROUND( 2 );
   ROUND( 3 );
   ROUND( 4 );
   ROUND( 5 );
  /*( ROUND( 6 );
   ROUND( 7 );
   ROUND( 8 );
   ROUND( 9 );
   ROUND( 10 );
   ROUND( 11 ); */
   
   for( i = 0; i < 8; ++i )
      S->h[i] = S->h[i] ^ v[i] ^ v[i + 8];
   
#undef G
#undef ROUND
   return 0;
}

/* inlen now in bytes */
int blake2b_update( blake2b_state *S, const uint8_t *in, uint64_t inlen )
{
   while( inlen > 0 )
   {
      size_t left = S->buflen;
      size_t fill = 2 * BLAKE2B_BLOCKBYTES - left;
      
      if( inlen > fill )
      {
         memcpy( S->buf + left, in, fill ); // Fill buffer
         S->buflen += fill;
         blake2b_increment_counter( S, BLAKE2B_BLOCKBYTES );
         blake2b_compress( S, S->buf ); // Compress
         memcpy( S->buf, S->buf + BLAKE2B_BLOCKBYTES, BLAKE2B_BLOCKBYTES ); // Shift buffer left
         S->buflen -= BLAKE2B_BLOCKBYTES;
         in += fill;
         inlen -= fill;
      }
      else // inlen <= fill
      {
         memcpy( S->buf + left, in, inlen );
         S->buflen += inlen; // Be lazy, do not compress
         in += inlen;
         inlen -= inlen;
      }
   }
   
   return 0;
}
int blake2b_final( blake2b_state *S, uint8_t *out, uint8_t outlen )
{
   uint8_t buffer[BLAKE2B_OUTBYTES];
   
   if( S->buflen > BLAKE2B_BLOCKBYTES )
   {
      blake2b_increment_counter( S, BLAKE2B_BLOCKBYTES );
      blake2b_compress( S, S->buf );
      S->buflen -= BLAKE2B_BLOCKBYTES;
      memcpy( S->buf, S->buf + BLAKE2B_BLOCKBYTES, S->buflen );
   }
   
   blake2b_increment_counter( S, S->buflen );
   blake2b_set_lastblock( S );
   memset( S->buf + S->buflen, 0, 2 * BLAKE2B_BLOCKBYTES - S->buflen ); /* Padding */
   blake2b_compress( S, S->buf );
   
   for( int i = 0; i < 8; ++i ) /* Output full hash to temp buffer */
      store64( buffer + sizeof( S->h[i] ) * i, S->h[i] );
   
   memcpy( out, buffer, outlen );
   return 0;
}

/* inlen, at least, should be uint64_t. Others can be size_t. */
int blake2b( uint8_t *out, const void *in, const void *key, const uint8_t outlen, const uint64_t inlen, uint8_t keylen )
{
   blake2b_state S[1];
   
   /* Verify parameters */
   if ( NULL == in ) return -1;
   
   if ( NULL == out ) return -1;
   
   if( NULL == key ) keylen = 0;
   
   if( keylen > 0 )
   {
      if( blake2b_init_key( S, outlen, key, keylen ) < 0 ) return -1;
   }
   else
   {
      if( blake2b_init( S, outlen ) < 0 ) return -1;
   }
   
   blake2b_update( S, ( uint8_t * )in, inlen );
   blake2b_final( S, out, outlen );
   return 0;
}
void pthash(uchar hsh[]) {
   int ii;
   printf("0x");
   for (ii= 0; ii < hsz; ii++)
      printf("%02x",hsh[ii]);
   printf("\n");
}

void ptnode(ulint tx) {
   printf("[%llu] ",tx);
   pthash(tree(tx).chsh);
   printf(", ");
   pthash(tree(tx).thsh);
   printf("\n");
}
void hashxor5(uchar *rc,uchar *ac,uchar *bc,uchar *cc,uchar *dc,uchar *lc) {
   ulint *r, *a, *b, *c, *d, *l;
   int ii;
   r= (ulint *)rc;
   a= (ulint *)ac;
   b= (ulint *)bc;
   c= (ulint *)cc;
   d= (ulint *)dc;
   l= (ulint *)lc;
   for (ii= 0; ii < hwds; ii++)
      r[ii]= a[ii] ^ b[ii] ^ c[ii] ^ d[ii] ^ l[ii];
}
uint hasheq(uchar *x,uchar *y) {
   int ii;
   for (ii= 0; ii < hsz; ii++)
      if (x[ii] != y[ii])
         return 1;
   return 0;
}
void hash2(unsigned char hh[],unsigned char ha[],unsigned char hb[]) {
   memmove(hashbuf,ha,hsz);
   memmove(&hashbuf[hsz],hb,hsz);
   blake2b(hh,hashbuf,0,hsz,hsz+hsz,0);
}
void hashn(unsigned char hh[], ulint nn, unsigned char cc[], unsigned char ha[]) {
   memmove(cc,&nn,sizeof(ulint));
   hash2(hh, cc, ha);
}
void hashnx(uchar hh[], ulint tx, uchar nn[], uchar ha[],uchar hb[],uchar hc[],uchar hd[], uchar hl[]) {
   hashxor5(hh,ha,hb,hc,hd,hl);
   hashn(hh,tx,nn,hh);
}
#define INBUF 0
#define UTBUF 1
#define readbuf(rw,bno) {wl= pread(Pfd,treebufs[rw],dopebyts,bno*dopebyts); \
                         if (wl != dopebyts) { \
                             printf("Read Error %llu",wl); \
                             return 1;} \
                         treedope[bno]= treebufs[rw];}
node ttree(ulint nx) {
   ulint wl;
   toffs= (nx > kd4 ? nx-kd4 : 0);
   tlim= (nx + kd2 < treesz ? nx+kd2 : treesz-1);
   wl= pread(Pfd, tbuf, (tlim-toffs+1)*sizeof(node), toffs*sizeof(node));
   if (wl < (tlim-toffs+1)*sizeof(node))
      printf("rd err %llu %llu",wl,nx);
   return tbuf[nx-toffs];
}
#define treet(x) (((x) <= tlim) && ((x) >= toffs) ? tbuf[(x)-toffs] : ttree(x))
int init() {
    ulint tx,wl,rb,wb;
    int Rfd, cr;
    node t1, *tt;
    uchar cb= 0;
   
    memset(num,0,hsz);
    treedope= (node**)calloc(dopes,sizeof(node *));
    treebufs= malloc(bufs*sizeof(node *));
    for (tx=0; tx < bufs; tx++)
       treebufs[tx]= (node *)malloc(dopebyts);
    Pfd= open(Proof,O_RDONLY,0700);
    if (Pfd >= 0) {
       printf("Proof Present\n");
       cr= close(Pfd);
       if (cr != 0)
          printf("Close Error %d\n",cr);
       tbuf= (node *)malloc((kd4+kd2+1)*sizeof(node));
       return 0;
    }
    Rfd= open(Roots,O_RDONLY,0700);
    if (Rfd >= 0) {
       printf("Roots Present\n");
       abort();
    }
    treedope[0]= treebufs[0];
    memset(treedope[0][0].thsh,0,hsz);
    memmove(treedope[0][0].chsh,id,hsz);
    Pfd= creat(Proof,0700);
    for (tx= 1; tx < kd4; tx++)
       hashn(treedope[0][tx].chsh,tx,num,treedope[0][tx-1].chsh);
    wb= 0;
    for (tx= kd4+1; tx < treesz; tx++) {
       hashnx(tree(tx).chsh,tx,num,tree(tx-kd1).chsh,tree(tx-kd2).chsh,tree(tx-kd3).chsh,tree(tx-kd4).chsh,tree(tx-1).chsh);
       if (((tx + 1) & (dopesz - 1)) == 0) {
          printf("a row=%llu\n",wb);
          wl= write(Pfd,treedope[wb],dopebyts);
          if (wl != dopebyts)
             printf("Write Rslt %llu\n",wl);
          cb= (cb+1)&1;
          if (wb > 0)
             treedope[wb-1]= NULL;
          treedope[++wb]= treebufs[cb];
       }
    }
    cr= close(Pfd);
    if (cr != 0)
       printf("Close Error %d\n",cr);
    Pfd= open(Proof,O_RDWR,0700);
    if (Pfd <= 0) {
       printf("Proof Reopen Error\n");
       return 1;
    }
    wb= (treesz>>1)>>dopepwr;
    readbuf(UTBUF,wb);
    rb= 0;
    readbuf(INBUF,0);
    t1= tree(1);
    for (tx= (treesz>>1) +1; tx <= ((treesz>>1)+(treesz>>2)); tx ++) {
       hash2(tree(tx).thsh,t1.chsh,tree(((tx-(treesz>>1))<<1)).chsh);
       t1= tree((((tx+1)-(treesz>>1))<<1)-1);
       if (tx&1) { // odd
          if (((tx +1) & ((dopesz>>1) -1)) == 0) {
             if (((tx +1) & (dopesz - 1)) == 0) {
                printf("b row=%llu\n",tx>>dopepwr);
                wl= pwrite(Pfd,treedope[tx>>dopepwr],dopebyts,(tx>>dopepwr)*dopebyts);
                if (wl != dopebyts)
                   printf("Write Rslt %llu\n",wl);
                treedope[wb]= NULL;
                wb++;
                readbuf(UTBUF,wb);
             }
             rb++;
             readbuf(INBUF,rb);
          }
       }
    }
    t1= tree((((((treesz>>1)+(treesz>>2))+1)-(treesz>>1))<<1)-1);
    for (tx= ((treesz>>1)+(treesz>>2))+1; tx < treesz ; tx++) {
       hash2(tree(tx).thsh,t1.thsh,tree(((tx-(treesz>>1))<<1)).thsh);
       t1= tree((((tx+1)-(treesz>>1))<<1)-1);
       if (tx&1) { // odd
          if (((tx +1) & ((dopesz>>1) -1)) == 0) {
             if (((tx + 1) & (dopesz - 1)) == 0) {
                printf("c row=%llu\n",tx>>dopepwr);
                wl= pwrite(Pfd,treedope[tx>>dopepwr],dopebyts,(tx>>dopepwr)*dopebyts);
                if (wl != dopebyts)
                   printf("Write Rslt %llu\n",wl);
                if (tx < treesz-1) {
                   wb++;
                   readbuf(UTBUF,wb);
                   //need((tx+1) >> dopepwr,(tx >> dopepwr),(((tx+1)-(treesz>>1))<<1) >> dopepwr);
                }
             }
             if (tx < treesz-1) {
                treedope[rb]= NULL;
                rb++;
                if (rb != wb)
                   readbuf(INBUF,rb);
                //need((tx+1) >> dopepwr,(((tx+1)-(treesz>>1))<<1) >> dopepwr,norow);
             }
          }
       }
    }
   memmove(rhash+hsz,tree(treesz-1).thsh,hsz);
   tt= treebufs[INBUF]; // no need to read rb, it is the last wb
   treebufs[INBUF]= treebufs[UTBUF];
   treebufs[UTBUF]= tt;
   wb= ((treesz>>1) -1) >>dopepwr;
   readbuf(UTBUF,wb);
   for (tx= (treesz>>1) -1; tx >= treesz>>2; tx--) {
      hash2(tree(tx).thsh,tree(tx+tx).chsh,tree(tx+tx+1).chsh);
      if ((tx & ((dopesz>>1) -1)) == 0) {
         if ((tx & (dopesz-1)) == 0) {
            printf("d row=%llu\n",tx>>dopepwr);
            wl= pwrite(Pfd,treedope[tx>>dopepwr],dopebyts,tx*sizeof(node));
            if (wl != dopebyts)
               printf("Write Rslt %llu\n",wl);
            treedope[wb]= NULL;
            wb--;
            readbuf(UTBUF,wb);
         }
         treedope[rb]= NULL;
         rb--;
         readbuf(INBUF,rb);
      }
   }
   for (tx= (treesz>>2) -1; tx > 0; tx--) {
      hash2(tree(tx).thsh,tree(tx+tx).thsh,tree(tx+tx+1).thsh);
      if ((tx & ((dopesz>>1) -1)) == 0) {
         if ((tx & (dopesz-1)) == 0) {
            printf("e row=%llu\n",wb);
            wl= pwrite(Pfd,treedope[wb],dopebyts,tx*sizeof(node));
            if (wl != dopebyts)
               printf("Write Rslt %llu\n",wl);
            treedope[wb]= NULL;
            wb--;
            readbuf(UTBUF,wb);
         }
         rb--;
         if (rb > 0) {
            treedope[rb+1]= NULL;
            readbuf(INBUF,rb);
         }
         //need((tx-1) >> dopepwr,(tx-1) >> (dopepwr-1),norow);
      }
    }
    memmove(rhash,tree(1).thsh,hsz);
    Rfd= creat(Roots,0700);
    wl= write(Rfd,rhash,hsz+hsz);
    if (wl != (hsz+hsz))
       printf("Roots Error\n");
    close(Rfd);
    memset(rhash,0,hsz+hsz);
    wl= pwrite(Pfd,treedope[0],dopebyts,0);
    if (wl != dopebyts)
       printf("Write Rslt %llu\n",wl);
    treedope[0]= treedope[1]= NULL;
    for (rb=0;rb < bufs; rb++)
       free(treebufs[rb]);
    cr= close(Pfd);
    if (cr != 0)
       printf("Close Error %d\n",cr);
    printf("f row=0\n");
    tbuf= (node *)malloc((kd4+kd2+1)*sizeof(node));
    return cr;
}
void prover (ulint prf, uint bx, prnode chn[]) {
    ulint ii, tx= prf, xt, inv= (prf < (treesz>>1)), lo;
    chn[bx].ptreex= prf;
    memmove(&chn[bx].pchsh,treet(prf).chsh,hsz);
    if (prf >= kd4)
       hashxor5(chn[bx].pphsh,treet(prf-kd1).chsh,treet(prf-kd2).chsh,treet(prf-kd3).chsh,treet(tx-kd4).chsh,treet(prf-1).chsh);
    else
       memmove(&chn[bx].pphsh,treet(prf-1).chsh,hsz);
    prf= (inv ? treesz-prf : prf);
    for (ii= bx + 1; ii <= bx + treepwr -1; ii++) {
       xt= tx;
       prf>>= 1;
       tx= (inv ? treesz - prf : prf);
       chn[ii].ptreex= tx;
       memmove(&chn[ii].pchsh,treet(tx).chsh,hsz);
       if (tx >= kd4)
          hashxor5(chn[ii].pphsh,treet(tx-kd1).chsh,treet(tx-kd2).chsh,treet(tx-kd3).chsh,treet(tx-kd4).chsh,treet(tx-1).chsh);
       else
          memmove(&chn[ii].pphsh,treet(tx-1).chsh,hsz);
       lo= ((xt & 1) == 0) ^ inv;
       if (ii == bx +1)
          memmove(&chn[ii].pthsh,treet((lo ? xt + 1 : xt - 1)).chsh, hsz);
       else
          memmove(&chn[ii].pthsh,treet((lo ? xt + 1 : xt - 1)).thsh, hsz);
    }
}
ulint linker(ulint lnk, uint bx, prnode chn[]) {
   int ii;
   ulint ol;
   uchar *cp;
   for (ii= bx; ii < bx + hops - 1; ii++) {
      chn[ii].ptreex= ol= lnk;
      memmove(&chn[ii].pchsh,treet(lnk).chsh,hsz);
      if (lnk >= kd4)
         hashxor5(chn[ii].pphsh,treet(lnk-kd1).chsh,treet(lnk-kd2).chsh,treet(lnk-kd3).chsh,treet(lnk-kd4).chsh,treet(lnk-1).chsh);
      else
         memmove(&chn[ii].pphsh,treet(lnk-1).chsh,hsz);
      memmove(&chn[ii].pthsh,treet(lnk).thsh,hsz);
      cp= chn[ii].pchsh;
      lnk= *(cp + (ol % hsz));
      lnk<<= 8;
      cp= chn[ii].pthsh;
      lnk|= *(cp + ((ol+1) % hsz));
      lnk<<= 8;
      cp= chn[ii].pphsh;
      lnk= (((lnk | *(cp+((ol+2) % hsz)))%hopmod) + chn[ii].ptreex) & hopmsk;
   }
   chn[bx + hops -1].ptreex= lnk;
   memmove(&chn[bx + hops -1].pchsh,treet(lnk).chsh,hsz);
   if (lnk > kd4)
      hashxor5(chn[bx + hops -1].pphsh,treet(lnk-kd1).chsh,treet(lnk-kd2).chsh,treet(lnk-kd3).chsh,treet(lnk-kd4).chsh,treet(lnk-1).chsh);
   else
      memmove(&chn[bx + hops -1].pphsh,treet(lnk-1).chsh,hsz);
   memmove(&chn[bx + hops-1].pthsh,treet(lnk).thsh,hsz);
   return lnk;
}
ulint golink(uint bx, prnode chn[]) {
   int ii;
   ulint lnk, ol;
   prnode pn;
   uchar *cp;
   uchar temphsh[hsz];
   pn= chn[bx];
   ol= pn.ptreex;
   hashn(temphsh,ol,num,pn.pphsh);
   if (hasheq(temphsh,pn.pchsh) > 0)
      return errv;
   cp= pn.pchsh;
   lnk= *(cp + (ol % hsz));
   lnk<<= 8;
   cp= pn.pthsh;
   lnk|= *(cp + ((ol+1) % hsz));
   lnk<<= 8;
   cp= pn.pphsh;
   lnk= (((lnk|*(cp + ((ol+2) % hsz))) % hopmod) + pn.ptreex) & hopmsk;
   for (ii= 1; ii < hops - 1; ii++) {
      pn= chn[bx+ii];
      if (pn.ptreex != lnk)
         return errv;
      hashn(temphsh,pn.ptreex,num,pn.pphsh);
      if (hasheq(temphsh,pn.pchsh) > 0)
         return errv;
      cp= pn.pchsh;
      ol= lnk;
      lnk= *(cp + (ol % hsz));
      lnk<<= 8;
      cp= pn.pthsh;
      lnk|= *(cp + ((ol+1) % hsz));
      lnk<<= 8;
      cp= pn.pphsh;
      lnk= (((lnk|*(cp+((ol+2) % hsz)))%hopmod) + pn.ptreex) & hopmsk;
   }
   return lnk;
}
ulint goroot(ulint prf, uint bx, prnode chn[]) {
   uint ii;
   ulint inv, lo;
   prnode pn;
   uchar treehsh[hsz], temphsh[hsz];
   inv= (prf < (treesz>>1));
   for (ii= bx; ii < bx + treepwr; ii++) {
      pn= chn[ii];
      hashn(temphsh,pn.ptreex,num,pn.pphsh);
      if (hasheq(temphsh,pn.pchsh) > 0)
         return 1;
      if (ii > bx) {
         lo= ((chn[ii-1].ptreex & 1) != 0) ^ inv;
         if (lo)
            hash2(temphsh,chn[ii].pthsh,treehsh);
         else
            hash2(temphsh,treehsh,chn[ii].pthsh);
         memmove(treehsh,temphsh,hsz);
      }
      else
         memcpy(treehsh,chn[bx].pchsh,hsz);
   }
   if (hasheq(treehsh,&rhash[(prf > (treesz>>1) ? 0 : hsz)]) > 0)
      return 1;
   return 0;
}
ulint GetProof(ulint prf, prnode chn[]) {
   ulint prl;
   prover(prf,0,chn);
   prl= linker(prf,treepwr,chn);
   prover(prl,treepwr+hops,chn);
   return prl;
}
uint VerProof(ulint prf, ulint prl, prnode chn[]) {
   ulint pr2;
   if (goroot(prf,0,chn))
      return 1;
   pr2= golink(treepwr,chn);
   if (pr2 == errv || pr2 != prl)
      return 2;
   if (goroot(prl,treepwr+hops,chn))
      return 3;
   return 0;
}
int ver() {
   int cr, Rfd;
   uint ii,rr;
   ulint prf, prl, wl;
   prnode chn[hops+2*treepwr];
   Pfd= open(Proof,O_RDONLY,0700);
   if (Pfd <= 0) {
      printf("Proof Absent\n");
      cr= close(Pfd);
      if (cr != 0)
         printf("PClose Error %d\n",cr);
      return 1;
   }
   Rfd= open(Roots,O_RDONLY,0700);
   if (Rfd <= 0) {
      printf("Roots Absent\n");
      cr= close(Rfd);
      if (cr != 0)
         printf("RClose Error %d\n",cr);
      return 1;
   }
   wl= read(Rfd, rhash, hsz+hsz);
   if (wl != hsz+hsz) {
      printf("Roots Read\n");
      return 1;
   }
   for (ii= 0; ii< vers; ii++) {
      prf= (((ulint)(rand() * rand())) % (treesz-1)) +1;
      prl= GetProof(prf, chn);
      rr= VerProof(prf,prl,chn);
      if (rr > 0)
         return rr;
      //else
        // printf("Proof # %d\n",ii);
   }
   printf("# verified %d\n",vers);
   for (prl=0; prl < dopes; prl++)
      if (treedope[prl] != NULL)
         treedope[prl]= NULL;
   free(treedope);
   return 0;
}
int main(int argc, const char * argv[]) {
   clock_t clk;
   dopepwr= 24;
   treepwr= 22;
   if (argc > 1) {
      treepwr= atoi(argv[1]);
      if (argc > 2) {
         dopepwr= atoi(argv[2]);
      }
   }
   if (dopepwr > treepwr)
      dopepwr= treepwr;
   if (treepwr < 23)
      printf("TP:%d DP:%d Tree Size:%5.3f GB\n",treepwr,dopepwr,((float)1/(1<<(23-treepwr))));
   else
      printf("P:%d DP:%d Tree Size:%d GB\n",treepwr,dopepwr,1<<(treepwr-23));
   clk= -clock();
   if (init()) return EXIT_FAILURE;
   printf("init secs %lu\n",(clock()+clk)/CLOCKS_PER_SEC);
   clk= -clock();
   if (ver()) return EXIT_FAILURE;
   printf("prov/ver secs %2.1f\n",(float)(clock()+clk)/CLOCKS_PER_SEC);
   return EXIT_SUCCESS;
}

#include <math.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

typedef union {
  char sb[1];
  unsigned char ub[1];
} reg8_t;

typedef union {
  char sb[2];
  unsigned char ub[2];
  short sw[1];
  unsigned short uw[1];
} reg16_t;

typedef union {
  char sb[4];
  unsigned char ub[4];
  short sw[2];
  unsigned short uw[2];
  long int sd[1];
  unsigned long int ud[1];
  float ps[1];
} reg32_t;

typedef union {
  char sb[8];
  unsigned char ub[8];
  short sw[4];
  unsigned short uw[4];
  long int sd[2];
  unsigned long int ud[2];
  long long int sq[1];
  unsigned long long int uq[1];
  float ps[2];
  double pd[1];
} reg64_t __attribute__ ((aligned (8)));

typedef union {
  char sb[16];
  unsigned char ub[16];
  short sw[8];
  unsigned short uw[8];
  long int sd[4];
  unsigned long int ud[4];
  long long int sq[2];
  unsigned long long int uq[2];
  float ps[4];
  double pd[2];
} reg128_t __attribute__ ((aligned (16)));

static sigjmp_buf catchpoint;

static void handle_sigill(int signum)
{
   siglongjmp(catchpoint, 1);
}

__attribute__((unused))
static int eq_float(float f1, float f2)
{
   return f1 == f2 || fabsf(f1 - f2) < fabsf(f1) * 1.5 * pow(2,-12);
}

__attribute__((unused))
static int eq_double(double d1, double d2)
{
   return d1 == d2 || fabs(d1 - d2) < fabs(d1) * 1.5 * pow(2,-12);
}

static void psignb_1(void)
{
   reg64_t arg0 = { .ub = { 0U, 10U, 0U, 245U, 0U, 1U, 255U, 254U } };
   reg64_t arg1 = { .ub = { 0U, 40U, 80U, 120U, 160U, 200U, 240U, 24U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "psignb %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sb[0] == 0 && result0.sb[1] == 40 && result0.sb[2] == 0 && result0.sb[3] == -120 && result0.sb[4] == 0 && result0.sb[5] == -56 && result0.sb[6] == 16 && result0.sb[7] == -24 )
      {
         printf("psignb_1 ... ok\n");
      }
      else
      {
         printf("psignb_1 ... not ok\n");
         printf("  result0.sb[0] = %d (expected %d)\n", result0.sb[0], 0);
         printf("  result0.sb[1] = %d (expected %d)\n", result0.sb[1], 40);
         printf("  result0.sb[2] = %d (expected %d)\n", result0.sb[2], 0);
         printf("  result0.sb[3] = %d (expected %d)\n", result0.sb[3], -120);
         printf("  result0.sb[4] = %d (expected %d)\n", result0.sb[4], 0);
         printf("  result0.sb[5] = %d (expected %d)\n", result0.sb[5], -56);
         printf("  result0.sb[6] = %d (expected %d)\n", result0.sb[6], 16);
         printf("  result0.sb[7] = %d (expected %d)\n", result0.sb[7], -24);
      }
   }
   else
   {
      printf("psignb_1 ... failed\n");
   }

   return;
}

static void psignb_2(void)
{
   reg64_t arg0 = { .ub = { 0U, 10U, 0U, 245U, 0U, 1U, 255U, 254U } };
   reg64_t arg1 = { .ub = { 0U, 41U, 79U, 119U, 161U, 199U, 241U, 23U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "psignb %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sb[0] == 0 && result0.sb[1] == 41 && result0.sb[2] == 0 && result0.sb[3] == -119 && result0.sb[4] == 0 && result0.sb[5] == -57 && result0.sb[6] == 15 && result0.sb[7] == -23 )
      {
         printf("psignb_2 ... ok\n");
      }
      else
      {
         printf("psignb_2 ... not ok\n");
         printf("  result0.sb[0] = %d (expected %d)\n", result0.sb[0], 0);
         printf("  result0.sb[1] = %d (expected %d)\n", result0.sb[1], 41);
         printf("  result0.sb[2] = %d (expected %d)\n", result0.sb[2], 0);
         printf("  result0.sb[3] = %d (expected %d)\n", result0.sb[3], -119);
         printf("  result0.sb[4] = %d (expected %d)\n", result0.sb[4], 0);
         printf("  result0.sb[5] = %d (expected %d)\n", result0.sb[5], -57);
         printf("  result0.sb[6] = %d (expected %d)\n", result0.sb[6], 15);
         printf("  result0.sb[7] = %d (expected %d)\n", result0.sb[7], -23);
      }
   }
   else
   {
      printf("psignb_2 ... failed\n");
   }

   return;
}

static void psignb_3(void)
{
   reg128_t arg0 = { .ub = { 0U, 10U, 0U, 245U, 0U, 1U, 255U, 254U, 1U, 255U, 254U, 0U, 10U, 0U, 245U, 0U } };
   reg128_t arg1 = { .ub = { 0U, 40U, 80U, 120U, 160U, 200U, 240U, 24U, 3U, 2U, 1U, 0U, 255U, 254U, 253U, 252U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "psignb %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sb[0] == 0 && result0.sb[1] == 40 && result0.sb[2] == 0 && result0.sb[3] == -120 && result0.sb[4] == 0 && result0.sb[5] == -56 && result0.sb[6] == 16 && result0.sb[7] == -24 && result0.sb[8] == 3 && result0.sb[9] == -2 && result0.sb[10] == -1 && result0.sb[11] == 0 && result0.sb[12] == -1 && result0.sb[13] == 0 && result0.sb[14] == 3 && result0.sb[15] == 0 )
      {
         printf("psignb_3 ... ok\n");
      }
      else
      {
         printf("psignb_3 ... not ok\n");
         printf("  result0.sb[0] = %d (expected %d)\n", result0.sb[0], 0);
         printf("  result0.sb[1] = %d (expected %d)\n", result0.sb[1], 40);
         printf("  result0.sb[2] = %d (expected %d)\n", result0.sb[2], 0);
         printf("  result0.sb[3] = %d (expected %d)\n", result0.sb[3], -120);
         printf("  result0.sb[4] = %d (expected %d)\n", result0.sb[4], 0);
         printf("  result0.sb[5] = %d (expected %d)\n", result0.sb[5], -56);
         printf("  result0.sb[6] = %d (expected %d)\n", result0.sb[6], 16);
         printf("  result0.sb[7] = %d (expected %d)\n", result0.sb[7], -24);
         printf("  result0.sb[8] = %d (expected %d)\n", result0.sb[8], 3);
         printf("  result0.sb[9] = %d (expected %d)\n", result0.sb[9], -2);
         printf("  result0.sb[10] = %d (expected %d)\n", result0.sb[10], -1);
         printf("  result0.sb[11] = %d (expected %d)\n", result0.sb[11], 0);
         printf("  result0.sb[12] = %d (expected %d)\n", result0.sb[12], -1);
         printf("  result0.sb[13] = %d (expected %d)\n", result0.sb[13], 0);
         printf("  result0.sb[14] = %d (expected %d)\n", result0.sb[14], 3);
         printf("  result0.sb[15] = %d (expected %d)\n", result0.sb[15], 0);
      }
   }
   else
   {
      printf("psignb_3 ... failed\n");
   }

   return;
}

static void psignb_4(void)
{
   reg128_t arg0 = { .ub = { 0U, 10U, 0U, 245U, 0U, 1U, 255U, 254U, 10U, 0U, 245U, 0U, 1U, 254U, 0U } };
   reg128_t arg1 = { .ub = { 0U, 41U, 79U, 119U, 161U, 199U, 241U, 23U, 0U, 31U, 69U, 109U, 151U, 189U, 231U, 13U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "psignb %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sb[0] == 0 && result0.sb[1] == 41 && result0.sb[2] == 0 && result0.sb[3] == -119 && result0.sb[4] == 0 && result0.sb[5] == -57 && result0.sb[6] == 15 && result0.sb[7] == -23 && result0.sb[8] == 0 && result0.sb[9] == 0 && result0.sb[10] == -69 && result0.sb[11] == 0 && result0.sb[12] == -105 && result0.sb[13] == 67 && result0.sb[14] == 0 )
      {
         printf("psignb_4 ... ok\n");
      }
      else
      {
         printf("psignb_4 ... not ok\n");
         printf("  result0.sb[0] = %d (expected %d)\n", result0.sb[0], 0);
         printf("  result0.sb[1] = %d (expected %d)\n", result0.sb[1], 41);
         printf("  result0.sb[2] = %d (expected %d)\n", result0.sb[2], 0);
         printf("  result0.sb[3] = %d (expected %d)\n", result0.sb[3], -119);
         printf("  result0.sb[4] = %d (expected %d)\n", result0.sb[4], 0);
         printf("  result0.sb[5] = %d (expected %d)\n", result0.sb[5], -57);
         printf("  result0.sb[6] = %d (expected %d)\n", result0.sb[6], 15);
         printf("  result0.sb[7] = %d (expected %d)\n", result0.sb[7], -23);
         printf("  result0.sb[8] = %d (expected %d)\n", result0.sb[8], 0);
         printf("  result0.sb[9] = %d (expected %d)\n", result0.sb[9], 0);
         printf("  result0.sb[10] = %d (expected %d)\n", result0.sb[10], -69);
         printf("  result0.sb[11] = %d (expected %d)\n", result0.sb[11], 0);
         printf("  result0.sb[12] = %d (expected %d)\n", result0.sb[12], -105);
         printf("  result0.sb[13] = %d (expected %d)\n", result0.sb[13], 67);
         printf("  result0.sb[14] = %d (expected %d)\n", result0.sb[14], 0);
      }
   }
   else
   {
      printf("psignb_4 ... failed\n");
   }

   return;
}

static void psignw_1(void)
{
   reg64_t arg0 = { .sw = { 0, 10, 0, -11 } };
   reg64_t arg1 = { .sw = { 999, 987, 986, 985 } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "psignw %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 0 && result0.sw[1] == 987 && result0.sw[2] == 0 && result0.sw[3] == -985 )
      {
         printf("psignw_1 ... ok\n");
      }
      else
      {
         printf("psignw_1 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 0);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 987);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 0);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], -985);
      }
   }
   else
   {
      printf("psignw_1 ... failed\n");
   }

   return;
}

static void psignw_2(void)
{
   reg64_t arg0 = { .sw = { 0, 1000, 0, -1111 } };
   reg64_t arg1 = { .sw = { 909, 907, 906, 905 } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "psignw %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 0 && result0.sw[1] == 907 && result0.sw[2] == 0 && result0.sw[3] == -905 )
      {
         printf("psignw_2 ... ok\n");
      }
      else
      {
         printf("psignw_2 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 0);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 907);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 0);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], -905);
      }
   }
   else
   {
      printf("psignw_2 ... failed\n");
   }

   return;
}

static void psignw_3(void)
{
   reg128_t arg0 = { .sw = { 0, 10, 0, -11, 1, 0, -1, 0 } };
   reg128_t arg1 = { .sw = { 999, 987, 986, 985, 888, 887, 886, 885 } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "psignw %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == 0 && result0.sw[1] == 987 && result0.sw[2] == 0 && result0.sw[3] == -985 && result0.sw[4] == 888 && result0.sw[5] == 0 && result0.sw[6] == -886 && result0.sw[7] == 0 )
      {
         printf("psignw_3 ... ok\n");
      }
      else
      {
         printf("psignw_3 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 0);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 987);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 0);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], -985);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 888);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 0);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], -886);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 0);
      }
   }
   else
   {
      printf("psignw_3 ... failed\n");
   }

   return;
}

static void psignw_4(void)
{
   reg128_t arg0 = { .sw = { 0, 1000, 0, -1111, 11, 0, -11, 0 } };
   reg128_t arg1 = { .sw = { 909, 907, 906, 905, 809, 808, 807, 806 } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "psignw %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == 0 && result0.sw[1] == 907 && result0.sw[2] == 0 && result0.sw[3] == -905 && result0.sw[4] == 809 && result0.sw[5] == 0 && result0.sw[6] == -807 )
      {
         printf("psignw_4 ... ok\n");
      }
      else
      {
         printf("psignw_4 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 0);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 907);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 0);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], -905);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 809);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 0);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], -807);
      }
   }
   else
   {
      printf("psignw_4 ... failed\n");
   }

   return;
}

static void psignd_1(void)
{
   reg64_t arg0 = { .sd = { 0L, 10000L } };
   reg64_t arg1 = { .sd = { -5555L, -6666L } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "psignd %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sd[0] == 0L && result0.sd[1] == -6666L )
      {
         printf("psignd_1 ... ok\n");
      }
      else
      {
         printf("psignd_1 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], 0L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], -6666L);
      }
   }
   else
   {
      printf("psignd_1 ... failed\n");
   }

   return;
}

static void psignd_2(void)
{
   reg64_t arg0 = { .sd = { -11111L, 0L } };
   reg64_t arg1 = { .sd = { -7777L, -8888L } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "psignd %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sd[0] == 7777L && result0.sd[1] == 0L )
      {
         printf("psignd_2 ... ok\n");
      }
      else
      {
         printf("psignd_2 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], 7777L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 0L);
      }
   }
   else
   {
      printf("psignd_2 ... failed\n");
   }

   return;
}

static void psignd_3(void)
{
   reg128_t arg0 = { .sd = { 0L, 10000L, -10000L, 0L } };
   reg128_t arg1 = { .sd = { -5555L, -6666L, -7777L, -8888L } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "psignd %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sd[0] == 0L && result0.sd[1] == -6666L && result0.sd[2] == 7777L && result0.sd[3] == 0L )
      {
         printf("psignd_3 ... ok\n");
      }
      else
      {
         printf("psignd_3 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], 0L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], -6666L);
         printf("  result0.sd[2] = %ld (expected %ld)\n", result0.sd[2], 7777L);
         printf("  result0.sd[3] = %ld (expected %ld)\n", result0.sd[3], 0L);
      }
   }
   else
   {
      printf("psignd_3 ... failed\n");
   }

   return;
}

static void psignd_4(void)
{
   reg128_t arg0 = { .sd = { -11111L, 0L, 0L, 1111L } };
   reg128_t arg1 = { .sd = { -9999L, -10101L, -11111L, -22222L } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "psignd %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sd[0] == 9999L && result0.sd[1] == 0L && result0.sd[2] == 0L && result0.sd[3] == -22222L )
      {
         printf("psignd_4 ... ok\n");
      }
      else
      {
         printf("psignd_4 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], 9999L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 0L);
         printf("  result0.sd[2] = %ld (expected %ld)\n", result0.sd[2], 0L);
         printf("  result0.sd[3] = %ld (expected %ld)\n", result0.sd[3], -22222L);
      }
   }
   else
   {
      printf("psignd_4 ... failed\n");
   }

   return;
}

static void pabsb_1(void)
{
   reg64_t arg0 = { .ub = { 0U, 10U, 0U, 245U, 0U, 1U, 255U, 254U } };
   reg64_t arg1 = { .ub = { 0U, 40U, 80U, 120U, 160U, 200U, 240U, 24U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "pabsb %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sb[0] == 0 && result0.sb[1] == 10 && result0.sb[2] == 0 && result0.sb[3] == 11 && result0.sb[4] == 0 && result0.sb[5] == 1 && result0.sb[6] == 1 && result0.sb[7] == 2 )
      {
         printf("pabsb_1 ... ok\n");
      }
      else
      {
         printf("pabsb_1 ... not ok\n");
         printf("  result0.sb[0] = %d (expected %d)\n", result0.sb[0], 0);
         printf("  result0.sb[1] = %d (expected %d)\n", result0.sb[1], 10);
         printf("  result0.sb[2] = %d (expected %d)\n", result0.sb[2], 0);
         printf("  result0.sb[3] = %d (expected %d)\n", result0.sb[3], 11);
         printf("  result0.sb[4] = %d (expected %d)\n", result0.sb[4], 0);
         printf("  result0.sb[5] = %d (expected %d)\n", result0.sb[5], 1);
         printf("  result0.sb[6] = %d (expected %d)\n", result0.sb[6], 1);
         printf("  result0.sb[7] = %d (expected %d)\n", result0.sb[7], 2);
      }
   }
   else
   {
      printf("pabsb_1 ... failed\n");
   }

   return;
}

static void pabsb_2(void)
{
   reg64_t arg0 = { .ub = { 0U, 10U, 0U, 245U, 0U, 1U, 255U, 254U } };
   reg64_t arg1 = { .ub = { 0U, 41U, 79U, 119U, 161U, 199U, 241U, 23U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "pabsb %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sb[0] == 0 && result0.sb[1] == 10 && result0.sb[2] == 0 && result0.sb[3] == 11 && result0.sb[4] == 0 && result0.sb[5] == 1 && result0.sb[6] == 1 && result0.sb[7] == 2 )
      {
         printf("pabsb_2 ... ok\n");
      }
      else
      {
         printf("pabsb_2 ... not ok\n");
         printf("  result0.sb[0] = %d (expected %d)\n", result0.sb[0], 0);
         printf("  result0.sb[1] = %d (expected %d)\n", result0.sb[1], 10);
         printf("  result0.sb[2] = %d (expected %d)\n", result0.sb[2], 0);
         printf("  result0.sb[3] = %d (expected %d)\n", result0.sb[3], 11);
         printf("  result0.sb[4] = %d (expected %d)\n", result0.sb[4], 0);
         printf("  result0.sb[5] = %d (expected %d)\n", result0.sb[5], 1);
         printf("  result0.sb[6] = %d (expected %d)\n", result0.sb[6], 1);
         printf("  result0.sb[7] = %d (expected %d)\n", result0.sb[7], 2);
      }
   }
   else
   {
      printf("pabsb_2 ... failed\n");
   }

   return;
}

static void pabsb_3(void)
{
   reg128_t arg0 = { .ub = { 0U, 10U, 0U, 245U, 0U, 1U, 255U, 254U, 1U, 255U, 254U, 0U, 10U, 0U, 245U, 0U } };
   reg128_t arg1 = { .ub = { 0U, 40U, 80U, 120U, 160U, 200U, 240U, 24U, 3U, 2U, 1U, 0U, 255U, 254U, 253U, 252U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pabsb %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sb[0] == 0 && result0.sb[1] == 10 && result0.sb[2] == 0 && result0.sb[3] == 11 && result0.sb[4] == 0 && result0.sb[5] == 1 && result0.sb[6] == 1 && result0.sb[7] == 2 && result0.sb[8] == 1 && result0.sb[9] == 1 && result0.sb[10] == 2 && result0.sb[11] == 0 && result0.sb[12] == 10 && result0.sb[13] == 0 && result0.sb[14] == 11 && result0.sb[15] == 0 )
      {
         printf("pabsb_3 ... ok\n");
      }
      else
      {
         printf("pabsb_3 ... not ok\n");
         printf("  result0.sb[0] = %d (expected %d)\n", result0.sb[0], 0);
         printf("  result0.sb[1] = %d (expected %d)\n", result0.sb[1], 10);
         printf("  result0.sb[2] = %d (expected %d)\n", result0.sb[2], 0);
         printf("  result0.sb[3] = %d (expected %d)\n", result0.sb[3], 11);
         printf("  result0.sb[4] = %d (expected %d)\n", result0.sb[4], 0);
         printf("  result0.sb[5] = %d (expected %d)\n", result0.sb[5], 1);
         printf("  result0.sb[6] = %d (expected %d)\n", result0.sb[6], 1);
         printf("  result0.sb[7] = %d (expected %d)\n", result0.sb[7], 2);
         printf("  result0.sb[8] = %d (expected %d)\n", result0.sb[8], 1);
         printf("  result0.sb[9] = %d (expected %d)\n", result0.sb[9], 1);
         printf("  result0.sb[10] = %d (expected %d)\n", result0.sb[10], 2);
         printf("  result0.sb[11] = %d (expected %d)\n", result0.sb[11], 0);
         printf("  result0.sb[12] = %d (expected %d)\n", result0.sb[12], 10);
         printf("  result0.sb[13] = %d (expected %d)\n", result0.sb[13], 0);
         printf("  result0.sb[14] = %d (expected %d)\n", result0.sb[14], 11);
         printf("  result0.sb[15] = %d (expected %d)\n", result0.sb[15], 0);
      }
   }
   else
   {
      printf("pabsb_3 ... failed\n");
   }

   return;
}

static void pabsb_4(void)
{
   reg128_t arg0 = { .ub = { 0U, 10U, 0U, 245U, 0U, 1U, 255U, 254U, 10U, 0U, 245U, 0U, 1U, 254U, 0U } };
   reg128_t arg1 = { .ub = { 0U, 41U, 79U, 119U, 161U, 199U, 241U, 23U, 0U, 31U, 69U, 109U, 151U, 189U, 231U, 13U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pabsb %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sb[0] == 0 && result0.sb[1] == 10 && result0.sb[2] == 0 && result0.sb[3] == 11 && result0.sb[4] == 0 && result0.sb[5] == 1 && result0.sb[6] == 1 && result0.sb[7] == 2 && result0.sb[8] == 10 && result0.sb[9] == 0 && result0.sb[10] == 11 && result0.sb[11] == 0 && result0.sb[12] == 1 && result0.sb[13] == 2 && result0.sb[14] == 0 )
      {
         printf("pabsb_4 ... ok\n");
      }
      else
      {
         printf("pabsb_4 ... not ok\n");
         printf("  result0.sb[0] = %d (expected %d)\n", result0.sb[0], 0);
         printf("  result0.sb[1] = %d (expected %d)\n", result0.sb[1], 10);
         printf("  result0.sb[2] = %d (expected %d)\n", result0.sb[2], 0);
         printf("  result0.sb[3] = %d (expected %d)\n", result0.sb[3], 11);
         printf("  result0.sb[4] = %d (expected %d)\n", result0.sb[4], 0);
         printf("  result0.sb[5] = %d (expected %d)\n", result0.sb[5], 1);
         printf("  result0.sb[6] = %d (expected %d)\n", result0.sb[6], 1);
         printf("  result0.sb[7] = %d (expected %d)\n", result0.sb[7], 2);
         printf("  result0.sb[8] = %d (expected %d)\n", result0.sb[8], 10);
         printf("  result0.sb[9] = %d (expected %d)\n", result0.sb[9], 0);
         printf("  result0.sb[10] = %d (expected %d)\n", result0.sb[10], 11);
         printf("  result0.sb[11] = %d (expected %d)\n", result0.sb[11], 0);
         printf("  result0.sb[12] = %d (expected %d)\n", result0.sb[12], 1);
         printf("  result0.sb[13] = %d (expected %d)\n", result0.sb[13], 2);
         printf("  result0.sb[14] = %d (expected %d)\n", result0.sb[14], 0);
      }
   }
   else
   {
      printf("pabsb_4 ... failed\n");
   }

   return;
}

static void pabsw_1(void)
{
   reg64_t arg0 = { .sw = { 0, 10, 0, -11 } };
   reg64_t arg1 = { .sw = { 999, 987, 986, 985 } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "pabsw %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 0 && result0.sw[1] == 10 && result0.sw[2] == 0 && result0.sw[3] == 11 )
      {
         printf("pabsw_1 ... ok\n");
      }
      else
      {
         printf("pabsw_1 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 0);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 10);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 0);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 11);
      }
   }
   else
   {
      printf("pabsw_1 ... failed\n");
   }

   return;
}

static void pabsw_2(void)
{
   reg64_t arg0 = { .sw = { 0, 1000, 0, -1111 } };
   reg64_t arg1 = { .sw = { 909, 907, 906, 905 } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "pabsw %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 0 && result0.sw[1] == 1000 && result0.sw[2] == 0 && result0.sw[3] == 1111 )
      {
         printf("pabsw_2 ... ok\n");
      }
      else
      {
         printf("pabsw_2 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 0);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 1000);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 0);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 1111);
      }
   }
   else
   {
      printf("pabsw_2 ... failed\n");
   }

   return;
}

static void pabsw_3(void)
{
   reg128_t arg0 = { .sw = { 0, 10, 0, -11, 1, 0, -1, 0 } };
   reg128_t arg1 = { .sw = { 999, 987, 986, 985, 888, 887, 886, 885 } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pabsw %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == 0 && result0.sw[1] == 10 && result0.sw[2] == 0 && result0.sw[3] == 11 && result0.sw[4] == 1 && result0.sw[5] == 0 && result0.sw[6] == 1 && result0.sw[7] == 0 )
      {
         printf("pabsw_3 ... ok\n");
      }
      else
      {
         printf("pabsw_3 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 0);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 10);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 0);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 11);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 1);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 0);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], 1);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 0);
      }
   }
   else
   {
      printf("pabsw_3 ... failed\n");
   }

   return;
}

static void pabsw_4(void)
{
   reg128_t arg0 = { .sw = { 0, 1000, 0, -1111, 11, 0, -11, 0 } };
   reg128_t arg1 = { .sw = { 909, 907, 906, 905, 809, 808, 807, 806 } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pabsw %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == 0 && result0.sw[1] == 1000 && result0.sw[2] == 0 && result0.sw[3] == 1111 && result0.sw[4] == 11 && result0.sw[5] == 0 && result0.sw[6] == 11 )
      {
         printf("pabsw_4 ... ok\n");
      }
      else
      {
         printf("pabsw_4 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 0);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 1000);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 0);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 1111);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 11);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 0);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], 11);
      }
   }
   else
   {
      printf("pabsw_4 ... failed\n");
   }

   return;
}

static void pabsd_1(void)
{
   reg64_t arg0 = { .sd = { 0L, 10000L } };
   reg64_t arg1 = { .sd = { -5555L, -6666L } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "pabsd %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sd[0] == 0L && result0.sd[1] == 10000L )
      {
         printf("pabsd_1 ... ok\n");
      }
      else
      {
         printf("pabsd_1 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], 0L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 10000L);
      }
   }
   else
   {
      printf("pabsd_1 ... failed\n");
   }

   return;
}

static void pabsd_2(void)
{
   reg64_t arg0 = { .sd = { -11111L, 0L } };
   reg64_t arg1 = { .sd = { -7777L, -8888L } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "pabsd %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sd[0] == 11111L && result0.sd[1] == 0L )
      {
         printf("pabsd_2 ... ok\n");
      }
      else
      {
         printf("pabsd_2 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], 11111L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 0L);
      }
   }
   else
   {
      printf("pabsd_2 ... failed\n");
   }

   return;
}

static void pabsd_3(void)
{
   reg128_t arg0 = { .sd = { 0L, 14000L, -10700L, 0L } };
   reg128_t arg1 = { .sd = { -5555L, -6666L, -7777L, -8888L } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pabsd %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sd[0] == 0L && result0.sd[1] == 14000L && result0.sd[2] == 10700L && result0.sd[3] == 0L )
      {
         printf("pabsd_3 ... ok\n");
      }
      else
      {
         printf("pabsd_3 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], 0L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 14000L);
         printf("  result0.sd[2] = %ld (expected %ld)\n", result0.sd[2], 10700L);
         printf("  result0.sd[3] = %ld (expected %ld)\n", result0.sd[3], 0L);
      }
   }
   else
   {
      printf("pabsd_3 ... failed\n");
   }

   return;
}

static void pabsd_4(void)
{
   reg128_t arg0 = { .sd = { -11111L, 0L, 0L, 1111L } };
   reg128_t arg1 = { .sd = { -9999L, -10101L, -11111L, -22222L } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pabsd %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sd[0] == 11111L && result0.sd[1] == 0L && result0.sd[2] == 0L && result0.sd[3] == 1111L )
      {
         printf("pabsd_4 ... ok\n");
      }
      else
      {
         printf("pabsd_4 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], 11111L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 0L);
         printf("  result0.sd[2] = %ld (expected %ld)\n", result0.sd[2], 0L);
         printf("  result0.sd[3] = %ld (expected %ld)\n", result0.sd[3], 1111L);
      }
   }
   else
   {
      printf("pabsd_4 ... failed\n");
   }

   return;
}

static void palignr_1(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $0, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0xffeeddccbbaa9988ULL )
      {
         printf("palignr_1 ... ok\n");
      }
      else
      {
         printf("palignr_1 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0xffeeddccbbaa9988ULL);
      }
   }
   else
   {
      printf("palignr_1 ... failed\n");
   }

   return;
}

static void palignr_2(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $1, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x34ffeeddccbbaa99ULL )
      {
         printf("palignr_2 ... ok\n");
      }
      else
      {
         printf("palignr_2 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x34ffeeddccbbaa99ULL);
      }
   }
   else
   {
      printf("palignr_2 ... failed\n");
   }

   return;
}

static void palignr_3(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $2, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x1134ffeeddccbbaaULL )
      {
         printf("palignr_3 ... ok\n");
      }
      else
      {
         printf("palignr_3 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x1134ffeeddccbbaaULL);
      }
   }
   else
   {
      printf("palignr_3 ... failed\n");
   }

   return;
}

static void palignr_4(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $3, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x221134ffeeddccbbULL )
      {
         printf("palignr_4 ... ok\n");
      }
      else
      {
         printf("palignr_4 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x221134ffeeddccbbULL);
      }
   }
   else
   {
      printf("palignr_4 ... failed\n");
   }

   return;
}

static void palignr_5(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $4, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x33221134ffeeddccULL )
      {
         printf("palignr_5 ... ok\n");
      }
      else
      {
         printf("palignr_5 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x33221134ffeeddccULL);
      }
   }
   else
   {
      printf("palignr_5 ... failed\n");
   }

   return;
}

static void palignr_6(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $5, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x4433221134ffeeddULL )
      {
         printf("palignr_6 ... ok\n");
      }
      else
      {
         printf("palignr_6 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x4433221134ffeeddULL);
      }
   }
   else
   {
      printf("palignr_6 ... failed\n");
   }

   return;
}

static void palignr_7(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $6, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x554433221134ffeeULL )
      {
         printf("palignr_7 ... ok\n");
      }
      else
      {
         printf("palignr_7 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x554433221134ffeeULL);
      }
   }
   else
   {
      printf("palignr_7 ... failed\n");
   }

   return;
}

static void palignr_8(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $7, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x66554433221134ffULL )
      {
         printf("palignr_8 ... ok\n");
      }
      else
      {
         printf("palignr_8 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x66554433221134ffULL);
      }
   }
   else
   {
      printf("palignr_8 ... failed\n");
   }

   return;
}

static void palignr_9(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $8, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x7766554433221134ULL )
      {
         printf("palignr_9 ... ok\n");
      }
      else
      {
         printf("palignr_9 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x7766554433221134ULL);
      }
   }
   else
   {
      printf("palignr_9 ... failed\n");
   }

   return;
}

static void palignr_10(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $9, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x77665544332211ULL )
      {
         printf("palignr_10 ... ok\n");
      }
      else
      {
         printf("palignr_10 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x77665544332211ULL);
      }
   }
   else
   {
      printf("palignr_10 ... failed\n");
   }

   return;
}

static void palignr_11(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $10, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x776655443322ULL )
      {
         printf("palignr_11 ... ok\n");
      }
      else
      {
         printf("palignr_11 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x776655443322ULL);
      }
   }
   else
   {
      printf("palignr_11 ... failed\n");
   }

   return;
}

static void palignr_12(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $11, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x7766554433ULL )
      {
         printf("palignr_12 ... ok\n");
      }
      else
      {
         printf("palignr_12 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x7766554433ULL);
      }
   }
   else
   {
      printf("palignr_12 ... failed\n");
   }

   return;
}

static void palignr_13(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $12, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x77665544ULL )
      {
         printf("palignr_13 ... ok\n");
      }
      else
      {
         printf("palignr_13 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x77665544ULL);
      }
   }
   else
   {
      printf("palignr_13 ... failed\n");
   }

   return;
}

static void palignr_14(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $13, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x776655ULL )
      {
         printf("palignr_14 ... ok\n");
      }
      else
      {
         printf("palignr_14 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x776655ULL);
      }
   }
   else
   {
      printf("palignr_14 ... failed\n");
   }

   return;
}

static void palignr_15(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $14, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x7766ULL )
      {
         printf("palignr_15 ... ok\n");
      }
      else
      {
         printf("palignr_15 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x7766ULL);
      }
   }
   else
   {
      printf("palignr_15 ... failed\n");
   }

   return;
}

static void palignr_16(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $15, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x77ULL )
      {
         printf("palignr_16 ... ok\n");
      }
      else
      {
         printf("palignr_16 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x77ULL);
      }
   }
   else
   {
      printf("palignr_16 ... failed\n");
   }

   return;
}

static void palignr_17(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $16, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_17 ... ok\n");
      }
      else
      {
         printf("palignr_17 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_17 ... failed\n");
   }

   return;
}

static void palignr_18(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $23, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_18 ... ok\n");
      }
      else
      {
         printf("palignr_18 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_18 ... failed\n");
   }

   return;
}

static void palignr_19(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $53, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_19 ... ok\n");
      }
      else
      {
         printf("palignr_19 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_19 ... failed\n");
   }

   return;
}

static void palignr_20(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $91, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_20 ... ok\n");
      }
      else
      {
         printf("palignr_20 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_20 ... failed\n");
   }

   return;
}

static void palignr_21(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $137, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_21 ... ok\n");
      }
      else
      {
         printf("palignr_21 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_21 ... failed\n");
   }

   return;
}

static void palignr_22(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $193, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_22 ... ok\n");
      }
      else
      {
         printf("palignr_22 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_22 ... failed\n");
   }

   return;
}

static void palignr_23(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $241, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_23 ... ok\n");
      }
      else
      {
         printf("palignr_23 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_23 ... failed\n");
   }

   return;
}

static void palignr_24(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "palignr $255, %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_24 ... ok\n");
      }
      else
      {
         printf("palignr_24 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_24 ... failed\n");
   }

   return;
}

static void palignr_25(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $0, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0xffeeddccbbaa9988ULL )
      {
         printf("palignr_25 ... ok\n");
      }
      else
      {
         printf("palignr_25 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0xffeeddccbbaa9988ULL);
      }
   }
   else
   {
      printf("palignr_25 ... failed\n");
   }

   return;
}

static void palignr_26(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $1, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x34ffeeddccbbaa99ULL )
      {
         printf("palignr_26 ... ok\n");
      }
      else
      {
         printf("palignr_26 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x34ffeeddccbbaa99ULL);
      }
   }
   else
   {
      printf("palignr_26 ... failed\n");
   }

   return;
}

static void palignr_27(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $2, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x1134ffeeddccbbaaULL )
      {
         printf("palignr_27 ... ok\n");
      }
      else
      {
         printf("palignr_27 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x1134ffeeddccbbaaULL);
      }
   }
   else
   {
      printf("palignr_27 ... failed\n");
   }

   return;
}

static void palignr_28(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $3, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x221134ffeeddccbbULL )
      {
         printf("palignr_28 ... ok\n");
      }
      else
      {
         printf("palignr_28 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x221134ffeeddccbbULL);
      }
   }
   else
   {
      printf("palignr_28 ... failed\n");
   }

   return;
}

static void palignr_29(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $4, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x33221134ffeeddccULL )
      {
         printf("palignr_29 ... ok\n");
      }
      else
      {
         printf("palignr_29 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x33221134ffeeddccULL);
      }
   }
   else
   {
      printf("palignr_29 ... failed\n");
   }

   return;
}

static void palignr_30(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $5, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x4433221134ffeeddULL )
      {
         printf("palignr_30 ... ok\n");
      }
      else
      {
         printf("palignr_30 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x4433221134ffeeddULL);
      }
   }
   else
   {
      printf("palignr_30 ... failed\n");
   }

   return;
}

static void palignr_31(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $6, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x554433221134ffeeULL )
      {
         printf("palignr_31 ... ok\n");
      }
      else
      {
         printf("palignr_31 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x554433221134ffeeULL);
      }
   }
   else
   {
      printf("palignr_31 ... failed\n");
   }

   return;
}

static void palignr_32(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $7, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x66554433221134ffULL )
      {
         printf("palignr_32 ... ok\n");
      }
      else
      {
         printf("palignr_32 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x66554433221134ffULL);
      }
   }
   else
   {
      printf("palignr_32 ... failed\n");
   }

   return;
}

static void palignr_33(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $8, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x7766554433221134ULL )
      {
         printf("palignr_33 ... ok\n");
      }
      else
      {
         printf("palignr_33 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x7766554433221134ULL);
      }
   }
   else
   {
      printf("palignr_33 ... failed\n");
   }

   return;
}

static void palignr_34(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $9, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x77665544332211ULL )
      {
         printf("palignr_34 ... ok\n");
      }
      else
      {
         printf("palignr_34 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x77665544332211ULL);
      }
   }
   else
   {
      printf("palignr_34 ... failed\n");
   }

   return;
}

static void palignr_35(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $10, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x776655443322ULL )
      {
         printf("palignr_35 ... ok\n");
      }
      else
      {
         printf("palignr_35 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x776655443322ULL);
      }
   }
   else
   {
      printf("palignr_35 ... failed\n");
   }

   return;
}

static void palignr_36(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $11, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x7766554433ULL )
      {
         printf("palignr_36 ... ok\n");
      }
      else
      {
         printf("palignr_36 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x7766554433ULL);
      }
   }
   else
   {
      printf("palignr_36 ... failed\n");
   }

   return;
}

static void palignr_37(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $12, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x77665544ULL )
      {
         printf("palignr_37 ... ok\n");
      }
      else
      {
         printf("palignr_37 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x77665544ULL);
      }
   }
   else
   {
      printf("palignr_37 ... failed\n");
   }

   return;
}

static void palignr_38(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $13, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x776655ULL )
      {
         printf("palignr_38 ... ok\n");
      }
      else
      {
         printf("palignr_38 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x776655ULL);
      }
   }
   else
   {
      printf("palignr_38 ... failed\n");
   }

   return;
}

static void palignr_39(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $14, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x7766ULL )
      {
         printf("palignr_39 ... ok\n");
      }
      else
      {
         printf("palignr_39 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x7766ULL);
      }
   }
   else
   {
      printf("palignr_39 ... failed\n");
   }

   return;
}

static void palignr_40(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $15, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0x77ULL )
      {
         printf("palignr_40 ... ok\n");
      }
      else
      {
         printf("palignr_40 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0x77ULL);
      }
   }
   else
   {
      printf("palignr_40 ... failed\n");
   }

   return;
}

static void palignr_41(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $16, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_41 ... ok\n");
      }
      else
      {
         printf("palignr_41 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_41 ... failed\n");
   }

   return;
}

static void palignr_42(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $23, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_42 ... ok\n");
      }
      else
      {
         printf("palignr_42 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_42 ... failed\n");
   }

   return;
}

static void palignr_43(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $53, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_43 ... ok\n");
      }
      else
      {
         printf("palignr_43 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_43 ... failed\n");
   }

   return;
}

static void palignr_44(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $91, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_44 ... ok\n");
      }
      else
      {
         printf("palignr_44 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_44 ... failed\n");
   }

   return;
}

static void palignr_45(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $137, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_45 ... ok\n");
      }
      else
      {
         printf("palignr_45 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_45 ... failed\n");
   }

   return;
}

static void palignr_46(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $193, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_46 ... ok\n");
      }
      else
      {
         printf("palignr_46 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_46 ... failed\n");
   }

   return;
}

static void palignr_47(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $241, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_47 ... ok\n");
      }
      else
      {
         printf("palignr_47 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_47 ... failed\n");
   }

   return;
}

static void palignr_48(void)
{
   reg64_t arg1 = { .uq = { 0xFFEEDDCCBBAA9988ULL } };
   reg64_t arg2 = { .uq = { 0x7766554433221134ULL } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "palignr $255, %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uq[0] == 0ULL )
      {
         printf("palignr_48 ... ok\n");
      }
      else
      {
         printf("palignr_48 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
      }
   }
   else
   {
      printf("palignr_48 ... failed\n");
   }

   return;
}

static void palignr_49(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $0, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 5940417471140883427ULL && result0.uq[1] == 2114202203853458723ULL )
      {
         printf("palignr_49 ... ok\n");
      }
      else
      {
         printf("palignr_49 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 5940417471140883427ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 2114202203853458723ULL);
      }
   }
   else
   {
      printf("palignr_49 ... failed\n");
   }

   return;
}

static void palignr_50(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $1, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2545220547074121835ULL && result0.uq[1] == 440604166586370189ULL )
      {
         printf("palignr_50 ... ok\n");
      }
      else
      {
         printf("palignr_50 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2545220547074121835ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 440604166586370189ULL);
      }
   }
   else
   {
      printf("palignr_50 ... failed\n");
   }

   return;
}

static void palignr_51(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $2, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 10170063027109847264ULL && result0.uq[1] == 6991307731704737800ULL )
      {
         printf("palignr_51 ... ok\n");
      }
      else
      {
         printf("palignr_51 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 10170063027109847264ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 6991307731704737800ULL);
      }
   }
   else
   {
      printf("palignr_51 ... failed\n");
   }

   return;
}

static void palignr_52(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $3, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 616187561003071328ULL && result0.uq[1] == 2477267993116521456ULL )
      {
         printf("palignr_52 ... ok\n");
      }
      else
      {
         printf("palignr_52 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 616187561003071328ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 2477267993116521456ULL);
      }
   }
   else
   {
      printf("palignr_52 ... failed\n");
   }

   return;
}

static void palignr_53(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $4, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 17296229551762872887ULL && result0.uq[1] == 11899179844356220851ULL )
      {
         printf("palignr_53 ... ok\n");
      }
      else
      {
         printf("palignr_53 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 17296229551762872887ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 11899179844356220851ULL);
      }
   }
   else
   {
      printf("palignr_53 ... failed\n");
   }

   return;
}

static void palignr_54(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $5, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 12965872729475674266ULL && result0.uq[1] == 11215408247145846567ULL )
      {
         printf("palignr_54 ... ok\n");
      }
      else
      {
         printf("palignr_54 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 12965872729475674266ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 11215408247145846567ULL);
      }
   }
   else
   {
      printf("palignr_54 ... failed\n");
   }

   return;
}

static void palignr_55(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $6, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2860894107828703856ULL && result0.uq[1] == 16905287193340550487ULL )
      {
         printf("palignr_55 ... ok\n");
      }
      else
      {
         printf("palignr_55 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2860894107828703856ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 16905287193340550487ULL);
      }
   }
   else
   {
      printf("palignr_55 ... failed\n");
   }

   return;
}

static void palignr_56(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $7, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 6280186048908436306ULL && result0.uq[1] == 930727406554121757ULL )
      {
         printf("palignr_56 ... ok\n");
      }
      else
      {
         printf("palignr_56 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 6280186048908436306ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 930727406554121757ULL);
      }
   }
   else
   {
      printf("palignr_56 ... failed\n");
   }

   return;
}

static void palignr_57(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $8, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2114202203853458723ULL && result0.uq[1] == 7713798215990141190ULL )
      {
         printf("palignr_57 ... ok\n");
      }
      else
      {
         printf("palignr_57 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2114202203853458723ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 7713798215990141190ULL);
      }
   }
   else
   {
      printf("palignr_57 ... failed\n");
   }

   return;
}

static void palignr_58(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $9, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 440604166586370189ULL && result0.uq[1] == 2840378191760400993ULL )
      {
         printf("palignr_58 ... ok\n");
      }
      else
      {
         printf("palignr_58 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 440604166586370189ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 2840378191760400993ULL);
      }
   }
   else
   {
      printf("palignr_58 ... failed\n");
   }

   return;
}

static void palignr_59(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $10, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 6991307731704737800ULL && result0.uq[1] == 17304917796414268706ULL )
      {
         printf("palignr_59 ... ok\n");
      }
      else
      {
         printf("palignr_59 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 6991307731704737800ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 17304917796414268706ULL);
      }
   }
   else
   {
      printf("palignr_59 ... failed\n");
   }

   return;
}

static void palignr_60(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $11, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2477267993116521456ULL && result0.uq[1] == 9579199748148730789ULL )
      {
         printf("palignr_60 ... ok\n");
      }
      else
      {
         printf("palignr_60 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2477267993116521456ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 9579199748148730789ULL);
      }
   }
   else
   {
      printf("palignr_60 ... failed\n");
   }

   return;
}

static void palignr_61(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $12, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 11899179844356220851ULL && result0.uq[1] == 3640298450912602779ULL )
      {
         printf("palignr_61 ... ok\n");
      }
      else
      {
         printf("palignr_61 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 11899179844356220851ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 3640298450912602779ULL);
      }
   }
   else
   {
      printf("palignr_61 ... failed\n");
   }

   return;
}

static void palignr_62(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $13, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 11215408247145846567ULL && result0.uq[1] == 2103890142923787498ULL )
      {
         printf("palignr_62 ... ok\n");
      }
      else
      {
         printf("palignr_62 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 11215408247145846567ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 2103890142923787498ULL);
      }
   }
   else
   {
      printf("palignr_62 ... failed\n");
   }

   return;
}

static void palignr_63(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $14, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 16905287193340550487ULL && result0.uq[1] == 6061056220056742668ULL )
      {
         printf("palignr_63 ... ok\n");
      }
      else
      {
         printf("palignr_63 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 16905287193340550487ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 6061056220056742668ULL);
      }
   }
   else
   {
      printf("palignr_63 ... failed\n");
   }

   return;
}

static void palignr_64(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $15, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 930727406554121757ULL && result0.uq[1] == 15371943530938247019ULL )
      {
         printf("palignr_64 ... ok\n");
      }
      else
      {
         printf("palignr_64 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 930727406554121757ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 15371943530938247019ULL);
      }
   }
   else
   {
      printf("palignr_64 ... failed\n");
   }

   return;
}

static void palignr_65(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $16, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 7713798215990141190ULL && result0.uq[1] == 3446753574200340519ULL )
      {
         printf("palignr_65 ... ok\n");
      }
      else
      {
         printf("palignr_65 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 7713798215990141190ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 3446753574200340519ULL);
      }
   }
   else
   {
      printf("palignr_65 ... failed\n");
   }

   return;
}

static void palignr_66(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $17, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2840378191760400993ULL && result0.uq[1] == 13463881149220080ULL )
      {
         printf("palignr_66 ... ok\n");
      }
      else
      {
         printf("palignr_66 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2840378191760400993ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 13463881149220080ULL);
      }
   }
   else
   {
      printf("palignr_66 ... failed\n");
   }

   return;
}

static void palignr_67(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $18, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 17304917796414268706ULL && result0.uq[1] == 52593285739140ULL )
      {
         printf("palignr_67 ... ok\n");
      }
      else
      {
         printf("palignr_67 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 17304917796414268706ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 52593285739140ULL);
      }
   }
   else
   {
      printf("palignr_67 ... failed\n");
   }

   return;
}

static void palignr_68(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $19, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 9579199748148730789ULL && result0.uq[1] == 205442522418ULL )
      {
         printf("palignr_68 ... ok\n");
      }
      else
      {
         printf("palignr_68 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 9579199748148730789ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 205442522418ULL);
      }
   }
   else
   {
      printf("palignr_68 ... failed\n");
   }

   return;
}

static void palignr_69(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $20, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 3640298450912602779ULL && result0.uq[1] == 802509853ULL )
      {
         printf("palignr_69 ... ok\n");
      }
      else
      {
         printf("palignr_69 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 3640298450912602779ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 802509853ULL);
      }
   }
   else
   {
      printf("palignr_69 ... failed\n");
   }

   return;
}

static void palignr_70(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $21, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2103890142923787498ULL && result0.uq[1] == 3134804ULL )
      {
         printf("palignr_70 ... ok\n");
      }
      else
      {
         printf("palignr_70 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2103890142923787498ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 3134804ULL);
      }
   }
   else
   {
      printf("palignr_70 ... failed\n");
   }

   return;
}

static void palignr_71(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $22, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 6061056220056742668ULL && result0.uq[1] == 12245ULL )
      {
         printf("palignr_71 ... ok\n");
      }
      else
      {
         printf("palignr_71 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 6061056220056742668ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 12245ULL);
      }
   }
   else
   {
      printf("palignr_71 ... failed\n");
   }

   return;
}

static void palignr_72(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $23, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 15371943530938247019ULL && result0.uq[1] == 47ULL )
      {
         printf("palignr_72 ... ok\n");
      }
      else
      {
         printf("palignr_72 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 15371943530938247019ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 47ULL);
      }
   }
   else
   {
      printf("palignr_72 ... failed\n");
   }

   return;
}

static void palignr_73(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $24, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 3446753574200340519ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_73 ... ok\n");
      }
      else
      {
         printf("palignr_73 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 3446753574200340519ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_73 ... failed\n");
   }

   return;
}

static void palignr_74(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $25, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 13463881149220080ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_74 ... ok\n");
      }
      else
      {
         printf("palignr_74 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 13463881149220080ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_74 ... failed\n");
   }

   return;
}

static void palignr_75(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $26, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 52593285739140ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_75 ... ok\n");
      }
      else
      {
         printf("palignr_75 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 52593285739140ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_75 ... failed\n");
   }

   return;
}

static void palignr_76(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $27, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 205442522418ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_76 ... ok\n");
      }
      else
      {
         printf("palignr_76 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 205442522418ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_76 ... failed\n");
   }

   return;
}

static void palignr_77(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $28, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 802509853ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_77 ... ok\n");
      }
      else
      {
         printf("palignr_77 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 802509853ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_77 ... failed\n");
   }

   return;
}

static void palignr_78(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $29, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 3134804ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_78 ... ok\n");
      }
      else
      {
         printf("palignr_78 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 3134804ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_78 ... failed\n");
   }

   return;
}

static void palignr_79(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $30, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 12245ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_79 ... ok\n");
      }
      else
      {
         printf("palignr_79 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 12245ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_79 ... failed\n");
   }

   return;
}

static void palignr_80(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $31, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 47ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_80 ... ok\n");
      }
      else
      {
         printf("palignr_80 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 47ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_80 ... failed\n");
   }

   return;
}

static void palignr_81(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $32, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_81 ... ok\n");
      }
      else
      {
         printf("palignr_81 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_81 ... failed\n");
   }

   return;
}

static void palignr_82(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $33, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_82 ... ok\n");
      }
      else
      {
         printf("palignr_82 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_82 ... failed\n");
   }

   return;
}

static void palignr_83(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $53, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_83 ... ok\n");
      }
      else
      {
         printf("palignr_83 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_83 ... failed\n");
   }

   return;
}

static void palignr_84(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $91, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_84 ... ok\n");
      }
      else
      {
         printf("palignr_84 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_84 ... failed\n");
   }

   return;
}

static void palignr_85(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $137, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_85 ... ok\n");
      }
      else
      {
         printf("palignr_85 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_85 ... failed\n");
   }

   return;
}

static void palignr_86(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $193, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_86 ... ok\n");
      }
      else
      {
         printf("palignr_86 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_86 ... failed\n");
   }

   return;
}

static void palignr_87(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $241, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_87 ... ok\n");
      }
      else
      {
         printf("palignr_87 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_87 ... failed\n");
   }

   return;
}

static void palignr_88(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $255, %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_88 ... ok\n");
      }
      else
      {
         printf("palignr_88 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_88 ... failed\n");
   }

   return;
}

static void palignr_89(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $0, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 5940417471140883427ULL && result0.uq[1] == 2114202203853458723ULL )
      {
         printf("palignr_89 ... ok\n");
      }
      else
      {
         printf("palignr_89 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 5940417471140883427ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 2114202203853458723ULL);
      }
   }
   else
   {
      printf("palignr_89 ... failed\n");
   }

   return;
}

static void palignr_90(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $1, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2545220547074121835ULL && result0.uq[1] == 440604166586370189ULL )
      {
         printf("palignr_90 ... ok\n");
      }
      else
      {
         printf("palignr_90 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2545220547074121835ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 440604166586370189ULL);
      }
   }
   else
   {
      printf("palignr_90 ... failed\n");
   }

   return;
}

static void palignr_91(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $2, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 10170063027109847264ULL && result0.uq[1] == 6991307731704737800ULL )
      {
         printf("palignr_91 ... ok\n");
      }
      else
      {
         printf("palignr_91 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 10170063027109847264ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 6991307731704737800ULL);
      }
   }
   else
   {
      printf("palignr_91 ... failed\n");
   }

   return;
}

static void palignr_92(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $3, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 616187561003071328ULL && result0.uq[1] == 2477267993116521456ULL )
      {
         printf("palignr_92 ... ok\n");
      }
      else
      {
         printf("palignr_92 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 616187561003071328ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 2477267993116521456ULL);
      }
   }
   else
   {
      printf("palignr_92 ... failed\n");
   }

   return;
}

static void palignr_93(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $4, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 17296229551762872887ULL && result0.uq[1] == 11899179844356220851ULL )
      {
         printf("palignr_93 ... ok\n");
      }
      else
      {
         printf("palignr_93 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 17296229551762872887ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 11899179844356220851ULL);
      }
   }
   else
   {
      printf("palignr_93 ... failed\n");
   }

   return;
}

static void palignr_94(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $5, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 12965872729475674266ULL && result0.uq[1] == 11215408247145846567ULL )
      {
         printf("palignr_94 ... ok\n");
      }
      else
      {
         printf("palignr_94 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 12965872729475674266ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 11215408247145846567ULL);
      }
   }
   else
   {
      printf("palignr_94 ... failed\n");
   }

   return;
}

static void palignr_95(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $6, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2860894107828703856ULL && result0.uq[1] == 16905287193340550487ULL )
      {
         printf("palignr_95 ... ok\n");
      }
      else
      {
         printf("palignr_95 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2860894107828703856ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 16905287193340550487ULL);
      }
   }
   else
   {
      printf("palignr_95 ... failed\n");
   }

   return;
}

static void palignr_96(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $7, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 6280186048908436306ULL && result0.uq[1] == 930727406554121757ULL )
      {
         printf("palignr_96 ... ok\n");
      }
      else
      {
         printf("palignr_96 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 6280186048908436306ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 930727406554121757ULL);
      }
   }
   else
   {
      printf("palignr_96 ... failed\n");
   }

   return;
}

static void palignr_97(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $8, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2114202203853458723ULL && result0.uq[1] == 7713798215990141190ULL )
      {
         printf("palignr_97 ... ok\n");
      }
      else
      {
         printf("palignr_97 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2114202203853458723ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 7713798215990141190ULL);
      }
   }
   else
   {
      printf("palignr_97 ... failed\n");
   }

   return;
}

static void palignr_98(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $9, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 440604166586370189ULL && result0.uq[1] == 2840378191760400993ULL )
      {
         printf("palignr_98 ... ok\n");
      }
      else
      {
         printf("palignr_98 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 440604166586370189ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 2840378191760400993ULL);
      }
   }
   else
   {
      printf("palignr_98 ... failed\n");
   }

   return;
}

static void palignr_99(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $10, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 6991307731704737800ULL && result0.uq[1] == 17304917796414268706ULL )
      {
         printf("palignr_99 ... ok\n");
      }
      else
      {
         printf("palignr_99 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 6991307731704737800ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 17304917796414268706ULL);
      }
   }
   else
   {
      printf("palignr_99 ... failed\n");
   }

   return;
}

static void palignr_100(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $11, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2477267993116521456ULL && result0.uq[1] == 9579199748148730789ULL )
      {
         printf("palignr_100 ... ok\n");
      }
      else
      {
         printf("palignr_100 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2477267993116521456ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 9579199748148730789ULL);
      }
   }
   else
   {
      printf("palignr_100 ... failed\n");
   }

   return;
}

static void palignr_101(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $12, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 11899179844356220851ULL && result0.uq[1] == 3640298450912602779ULL )
      {
         printf("palignr_101 ... ok\n");
      }
      else
      {
         printf("palignr_101 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 11899179844356220851ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 3640298450912602779ULL);
      }
   }
   else
   {
      printf("palignr_101 ... failed\n");
   }

   return;
}

static void palignr_102(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $13, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 11215408247145846567ULL && result0.uq[1] == 2103890142923787498ULL )
      {
         printf("palignr_102 ... ok\n");
      }
      else
      {
         printf("palignr_102 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 11215408247145846567ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 2103890142923787498ULL);
      }
   }
   else
   {
      printf("palignr_102 ... failed\n");
   }

   return;
}

static void palignr_103(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $14, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 16905287193340550487ULL && result0.uq[1] == 6061056220056742668ULL )
      {
         printf("palignr_103 ... ok\n");
      }
      else
      {
         printf("palignr_103 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 16905287193340550487ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 6061056220056742668ULL);
      }
   }
   else
   {
      printf("palignr_103 ... failed\n");
   }

   return;
}

static void palignr_104(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $15, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 930727406554121757ULL && result0.uq[1] == 15371943530938247019ULL )
      {
         printf("palignr_104 ... ok\n");
      }
      else
      {
         printf("palignr_104 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 930727406554121757ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 15371943530938247019ULL);
      }
   }
   else
   {
      printf("palignr_104 ... failed\n");
   }

   return;
}

static void palignr_105(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $16, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 7713798215990141190ULL && result0.uq[1] == 3446753574200340519ULL )
      {
         printf("palignr_105 ... ok\n");
      }
      else
      {
         printf("palignr_105 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 7713798215990141190ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 3446753574200340519ULL);
      }
   }
   else
   {
      printf("palignr_105 ... failed\n");
   }

   return;
}

static void palignr_106(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $17, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2840378191760400993ULL && result0.uq[1] == 13463881149220080ULL )
      {
         printf("palignr_106 ... ok\n");
      }
      else
      {
         printf("palignr_106 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2840378191760400993ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 13463881149220080ULL);
      }
   }
   else
   {
      printf("palignr_106 ... failed\n");
   }

   return;
}

static void palignr_107(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $18, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 17304917796414268706ULL && result0.uq[1] == 52593285739140ULL )
      {
         printf("palignr_107 ... ok\n");
      }
      else
      {
         printf("palignr_107 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 17304917796414268706ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 52593285739140ULL);
      }
   }
   else
   {
      printf("palignr_107 ... failed\n");
   }

   return;
}

static void palignr_108(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $19, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 9579199748148730789ULL && result0.uq[1] == 205442522418ULL )
      {
         printf("palignr_108 ... ok\n");
      }
      else
      {
         printf("palignr_108 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 9579199748148730789ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 205442522418ULL);
      }
   }
   else
   {
      printf("palignr_108 ... failed\n");
   }

   return;
}

static void palignr_109(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $20, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 3640298450912602779ULL && result0.uq[1] == 802509853ULL )
      {
         printf("palignr_109 ... ok\n");
      }
      else
      {
         printf("palignr_109 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 3640298450912602779ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 802509853ULL);
      }
   }
   else
   {
      printf("palignr_109 ... failed\n");
   }

   return;
}

static void palignr_110(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $21, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 2103890142923787498ULL && result0.uq[1] == 3134804ULL )
      {
         printf("palignr_110 ... ok\n");
      }
      else
      {
         printf("palignr_110 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 2103890142923787498ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 3134804ULL);
      }
   }
   else
   {
      printf("palignr_110 ... failed\n");
   }

   return;
}

static void palignr_111(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $22, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 6061056220056742668ULL && result0.uq[1] == 12245ULL )
      {
         printf("palignr_111 ... ok\n");
      }
      else
      {
         printf("palignr_111 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 6061056220056742668ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 12245ULL);
      }
   }
   else
   {
      printf("palignr_111 ... failed\n");
   }

   return;
}

static void palignr_112(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $23, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 15371943530938247019ULL && result0.uq[1] == 47ULL )
      {
         printf("palignr_112 ... ok\n");
      }
      else
      {
         printf("palignr_112 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 15371943530938247019ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 47ULL);
      }
   }
   else
   {
      printf("palignr_112 ... failed\n");
   }

   return;
}

static void palignr_113(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $24, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 3446753574200340519ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_113 ... ok\n");
      }
      else
      {
         printf("palignr_113 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 3446753574200340519ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_113 ... failed\n");
   }

   return;
}

static void palignr_114(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $25, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 13463881149220080ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_114 ... ok\n");
      }
      else
      {
         printf("palignr_114 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 13463881149220080ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_114 ... failed\n");
   }

   return;
}

static void palignr_115(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $26, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 52593285739140ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_115 ... ok\n");
      }
      else
      {
         printf("palignr_115 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 52593285739140ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_115 ... failed\n");
   }

   return;
}

static void palignr_116(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $27, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 205442522418ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_116 ... ok\n");
      }
      else
      {
         printf("palignr_116 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 205442522418ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_116 ... failed\n");
   }

   return;
}

static void palignr_117(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $28, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 802509853ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_117 ... ok\n");
      }
      else
      {
         printf("palignr_117 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 802509853ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_117 ... failed\n");
   }

   return;
}

static void palignr_118(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $29, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 3134804ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_118 ... ok\n");
      }
      else
      {
         printf("palignr_118 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 3134804ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_118 ... failed\n");
   }

   return;
}

static void palignr_119(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $30, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 12245ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_119 ... ok\n");
      }
      else
      {
         printf("palignr_119 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 12245ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_119 ... failed\n");
   }

   return;
}

static void palignr_120(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $31, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 47ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_120 ... ok\n");
      }
      else
      {
         printf("palignr_120 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 47ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_120 ... failed\n");
   }

   return;
}

static void palignr_121(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $32, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_121 ... ok\n");
      }
      else
      {
         printf("palignr_121 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_121 ... failed\n");
   }

   return;
}

static void palignr_122(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $33, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_122 ... ok\n");
      }
      else
      {
         printf("palignr_122 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_122 ... failed\n");
   }

   return;
}

static void palignr_123(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $53, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_123 ... ok\n");
      }
      else
      {
         printf("palignr_123 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_123 ... failed\n");
   }

   return;
}

static void palignr_124(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $91, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_124 ... ok\n");
      }
      else
      {
         printf("palignr_124 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_124 ... failed\n");
   }

   return;
}

static void palignr_125(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $137, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_125 ... ok\n");
      }
      else
      {
         printf("palignr_125 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_125 ... failed\n");
   }

   return;
}

static void palignr_126(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $193, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_126 ... ok\n");
      }
      else
      {
         printf("palignr_126 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_126 ... failed\n");
   }

   return;
}

static void palignr_127(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $241, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_127 ... ok\n");
      }
      else
      {
         printf("palignr_127 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_127 ... failed\n");
   }

   return;
}

static void palignr_128(void)
{
   reg128_t arg1 = { .uq = { 0x52709a3760e06be3ULL, 0x1d5727b3f0088d23ULL } };
   reg128_t arg2 = { .uq = { 0x6b0cea9ba5226106ULL, 0x2fd5541d3284f027ULL } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "palignr $255, %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg1), "m" (arg2), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uq[0] == 0ULL && result0.uq[1] == 0ULL )
      {
         printf("palignr_128 ... ok\n");
      }
      else
      {
         printf("palignr_128 ... not ok\n");
         printf("  result0.uq[0] = %llu (expected %llu)\n", result0.uq[0], 0ULL);
         printf("  result0.uq[1] = %llu (expected %llu)\n", result0.uq[1], 0ULL);
      }
   }
   else
   {
      printf("palignr_128 ... failed\n");
   }

   return;
}

static void pshufb_1(void)
{
   reg64_t arg0 = { .ub = { 14U, 6U, 4U, 3U, 1U, 0U, 255U, 128U } };
   reg64_t arg1 = { .ub = { 50U, 51U, 52U, 53U, 54U, 55U, 56U, 57U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "pshufb %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.ub[0] == 56U && result0.ub[1] == 56U && result0.ub[2] == 54U && result0.ub[3] == 53U && result0.ub[4] == 51U && result0.ub[5] == 50U && result0.ub[6] == 0U && result0.ub[7] == 0U )
      {
         printf("pshufb_1 ... ok\n");
      }
      else
      {
         printf("pshufb_1 ... not ok\n");
         printf("  result0.ub[0] = %u (expected %u)\n", result0.ub[0], 56U);
         printf("  result0.ub[1] = %u (expected %u)\n", result0.ub[1], 56U);
         printf("  result0.ub[2] = %u (expected %u)\n", result0.ub[2], 54U);
         printf("  result0.ub[3] = %u (expected %u)\n", result0.ub[3], 53U);
         printf("  result0.ub[4] = %u (expected %u)\n", result0.ub[4], 51U);
         printf("  result0.ub[5] = %u (expected %u)\n", result0.ub[5], 50U);
         printf("  result0.ub[6] = %u (expected %u)\n", result0.ub[6], 0U);
         printf("  result0.ub[7] = %u (expected %u)\n", result0.ub[7], 0U);
      }
   }
   else
   {
      printf("pshufb_1 ... failed\n");
   }

   return;
}

static void pshufb_2(void)
{
   reg64_t arg0 = { .ub = { 14U, 6U, 4U, 3U, 1U, 0U, 255U, 128U } };
   reg64_t arg1 = { .ub = { 50U, 51U, 52U, 53U, 54U, 55U, 56U, 57U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "pshufb %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.ub[0] == 56U && result0.ub[1] == 56U && result0.ub[2] == 54U && result0.ub[3] == 53U && result0.ub[4] == 51U && result0.ub[5] == 50U && result0.ub[6] == 0U && result0.ub[7] == 0U )
      {
         printf("pshufb_2 ... ok\n");
      }
      else
      {
         printf("pshufb_2 ... not ok\n");
         printf("  result0.ub[0] = %u (expected %u)\n", result0.ub[0], 56U);
         printf("  result0.ub[1] = %u (expected %u)\n", result0.ub[1], 56U);
         printf("  result0.ub[2] = %u (expected %u)\n", result0.ub[2], 54U);
         printf("  result0.ub[3] = %u (expected %u)\n", result0.ub[3], 53U);
         printf("  result0.ub[4] = %u (expected %u)\n", result0.ub[4], 51U);
         printf("  result0.ub[5] = %u (expected %u)\n", result0.ub[5], 50U);
         printf("  result0.ub[6] = %u (expected %u)\n", result0.ub[6], 0U);
         printf("  result0.ub[7] = %u (expected %u)\n", result0.ub[7], 0U);
      }
   }
   else
   {
      printf("pshufb_2 ... failed\n");
   }

   return;
}

static void pshufb_3(void)
{
   reg128_t arg0 = { .ub = { 63U, 31U, 15U, 14U, 8U, 7U, 1U, 0U, 255U, 128U, 127U, 126U, 123U, 231U, 213U, 103U } };
   reg128_t arg1 = { .ub = { 60U, 61U, 62U, 63U, 64U, 65U, 66U, 67U, 70U, 71U, 72U, 73U, 74U, 75U, 76U, 77U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pshufb %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.ub[0] == 77U && result0.ub[1] == 77U && result0.ub[2] == 77U && result0.ub[3] == 76U && result0.ub[4] == 70U && result0.ub[5] == 67U && result0.ub[6] == 61U && result0.ub[7] == 60U && result0.ub[8] == 0U && result0.ub[9] == 0U && result0.ub[10] == 77U && result0.ub[11] == 76U && result0.ub[12] == 73U && result0.ub[13] == 0U && result0.ub[14] == 0U && result0.ub[15] == 67U )
      {
         printf("pshufb_3 ... ok\n");
      }
      else
      {
         printf("pshufb_3 ... not ok\n");
         printf("  result0.ub[0] = %u (expected %u)\n", result0.ub[0], 77U);
         printf("  result0.ub[1] = %u (expected %u)\n", result0.ub[1], 77U);
         printf("  result0.ub[2] = %u (expected %u)\n", result0.ub[2], 77U);
         printf("  result0.ub[3] = %u (expected %u)\n", result0.ub[3], 76U);
         printf("  result0.ub[4] = %u (expected %u)\n", result0.ub[4], 70U);
         printf("  result0.ub[5] = %u (expected %u)\n", result0.ub[5], 67U);
         printf("  result0.ub[6] = %u (expected %u)\n", result0.ub[6], 61U);
         printf("  result0.ub[7] = %u (expected %u)\n", result0.ub[7], 60U);
         printf("  result0.ub[8] = %u (expected %u)\n", result0.ub[8], 0U);
         printf("  result0.ub[9] = %u (expected %u)\n", result0.ub[9], 0U);
         printf("  result0.ub[10] = %u (expected %u)\n", result0.ub[10], 77U);
         printf("  result0.ub[11] = %u (expected %u)\n", result0.ub[11], 76U);
         printf("  result0.ub[12] = %u (expected %u)\n", result0.ub[12], 73U);
         printf("  result0.ub[13] = %u (expected %u)\n", result0.ub[13], 0U);
         printf("  result0.ub[14] = %u (expected %u)\n", result0.ub[14], 0U);
         printf("  result0.ub[15] = %u (expected %u)\n", result0.ub[15], 67U);
      }
   }
   else
   {
      printf("pshufb_3 ... failed\n");
   }

   return;
}

static void pshufb_4(void)
{
   reg128_t arg0 = { .ub = { 63U, 31U, 15U, 14U, 8U, 7U, 1U, 0U, 255U, 128U, 127U, 126U, 123U, 231U, 213U, 103U } };
   reg128_t arg1 = { .ub = { 60U, 61U, 62U, 63U, 64U, 65U, 66U, 67U, 70U, 71U, 72U, 73U, 74U, 75U, 76U, 77U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pshufb %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.ub[0] == 77U && result0.ub[1] == 77U && result0.ub[2] == 77U && result0.ub[3] == 76U && result0.ub[4] == 70U && result0.ub[5] == 67U && result0.ub[6] == 61U && result0.ub[7] == 60U && result0.ub[8] == 0U && result0.ub[9] == 0U && result0.ub[10] == 77U && result0.ub[11] == 76U && result0.ub[12] == 73U && result0.ub[13] == 0U && result0.ub[14] == 0U && result0.ub[15] == 67U )
      {
         printf("pshufb_4 ... ok\n");
      }
      else
      {
         printf("pshufb_4 ... not ok\n");
         printf("  result0.ub[0] = %u (expected %u)\n", result0.ub[0], 77U);
         printf("  result0.ub[1] = %u (expected %u)\n", result0.ub[1], 77U);
         printf("  result0.ub[2] = %u (expected %u)\n", result0.ub[2], 77U);
         printf("  result0.ub[3] = %u (expected %u)\n", result0.ub[3], 76U);
         printf("  result0.ub[4] = %u (expected %u)\n", result0.ub[4], 70U);
         printf("  result0.ub[5] = %u (expected %u)\n", result0.ub[5], 67U);
         printf("  result0.ub[6] = %u (expected %u)\n", result0.ub[6], 61U);
         printf("  result0.ub[7] = %u (expected %u)\n", result0.ub[7], 60U);
         printf("  result0.ub[8] = %u (expected %u)\n", result0.ub[8], 0U);
         printf("  result0.ub[9] = %u (expected %u)\n", result0.ub[9], 0U);
         printf("  result0.ub[10] = %u (expected %u)\n", result0.ub[10], 77U);
         printf("  result0.ub[11] = %u (expected %u)\n", result0.ub[11], 76U);
         printf("  result0.ub[12] = %u (expected %u)\n", result0.ub[12], 73U);
         printf("  result0.ub[13] = %u (expected %u)\n", result0.ub[13], 0U);
         printf("  result0.ub[14] = %u (expected %u)\n", result0.ub[14], 0U);
         printf("  result0.ub[15] = %u (expected %u)\n", result0.ub[15], 67U);
      }
   }
   else
   {
      printf("pshufb_4 ... failed\n");
   }

   return;
}

static void pmulhrsw_1(void)
{
   reg64_t arg0 = { .ub = { 14U, 26U, 34U, 173U, 181U, 200U, 255U, 128U } };
   reg64_t arg1 = { .ub = { 50U, 151U, 52U, 153U, 54U, 155U, 56U, 157U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "pmulhrsw %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uw[0] == 60075 && result0.uw[1] == 17037 && result0.uw[2] == 11146 && result0.uw[3] == 25091 )
      {
         printf("pmulhrsw_1 ... ok\n");
      }
      else
      {
         printf("pmulhrsw_1 ... not ok\n");
         printf("  result0.uw[0] = %u (expected %u)\n", result0.uw[0], 60075);
         printf("  result0.uw[1] = %u (expected %u)\n", result0.uw[1], 17037);
         printf("  result0.uw[2] = %u (expected %u)\n", result0.uw[2], 11146);
         printf("  result0.uw[3] = %u (expected %u)\n", result0.uw[3], 25091);
      }
   }
   else
   {
      printf("pmulhrsw_1 ... failed\n");
   }

   return;
}

static void pmulhrsw_2(void)
{
   reg64_t arg0 = { .ub = { 14U, 26U, 34U, 173U, 181U, 200U, 255U, 128U } };
   reg64_t arg1 = { .ub = { 50U, 151U, 52U, 153U, 54U, 155U, 56U, 157U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "pmulhrsw %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.uw[0] == 60075 && result0.uw[1] == 17037 && result0.uw[2] == 11146 && result0.uw[3] == 25091 )
      {
         printf("pmulhrsw_2 ... ok\n");
      }
      else
      {
         printf("pmulhrsw_2 ... not ok\n");
         printf("  result0.uw[0] = %u (expected %u)\n", result0.uw[0], 60075);
         printf("  result0.uw[1] = %u (expected %u)\n", result0.uw[1], 17037);
         printf("  result0.uw[2] = %u (expected %u)\n", result0.uw[2], 11146);
         printf("  result0.uw[3] = %u (expected %u)\n", result0.uw[3], 25091);
      }
   }
   else
   {
      printf("pmulhrsw_2 ... failed\n");
   }

   return;
}

static void pmulhrsw_3(void)
{
   reg128_t arg0 = { .ub = { 14U, 26U, 34U, 173U, 181U, 200U, 255U, 128U, 24U, 36U, 44U, 183U, 191U, 210U, 9U, 138U } };
   reg128_t arg1 = { .ub = { 50U, 151U, 52U, 153U, 54U, 155U, 56U, 157U, 60U, 161U, 62U, 163U, 64U, 165U, 66U, 167U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pmulhrsw %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uw[0] == 60075 && result0.uw[1] == 17037 && result0.uw[2] == 11146 && result0.uw[3] == 25091 && result0.uw[4] == 58695 && result0.uw[5] == 13511 && result0.uw[6] == 8214 && result0.uw[7] == 20937 )
      {
         printf("pmulhrsw_3 ... ok\n");
      }
      else
      {
         printf("pmulhrsw_3 ... not ok\n");
         printf("  result0.uw[0] = %u (expected %u)\n", result0.uw[0], 60075);
         printf("  result0.uw[1] = %u (expected %u)\n", result0.uw[1], 17037);
         printf("  result0.uw[2] = %u (expected %u)\n", result0.uw[2], 11146);
         printf("  result0.uw[3] = %u (expected %u)\n", result0.uw[3], 25091);
         printf("  result0.uw[4] = %u (expected %u)\n", result0.uw[4], 58695);
         printf("  result0.uw[5] = %u (expected %u)\n", result0.uw[5], 13511);
         printf("  result0.uw[6] = %u (expected %u)\n", result0.uw[6], 8214);
         printf("  result0.uw[7] = %u (expected %u)\n", result0.uw[7], 20937);
      }
   }
   else
   {
      printf("pmulhrsw_3 ... failed\n");
   }

   return;
}

static void pmulhrsw_4(void)
{
   reg128_t arg0 = { .ub = { 14U, 26U, 34U, 173U, 181U, 200U, 255U, 128U, 24U, 36U, 44U, 183U, 191U, 210U, 9U, 138U } };
   reg128_t arg1 = { .ub = { 50U, 151U, 52U, 153U, 54U, 155U, 56U, 157U, 60U, 161U, 62U, 163U, 64U, 165U, 66U, 167U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pmulhrsw %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.uw[0] == 60075 && result0.uw[1] == 17037 && result0.uw[2] == 11146 && result0.uw[3] == 25091 && result0.uw[4] == 58695 && result0.uw[5] == 13511 && result0.uw[6] == 8214 && result0.uw[7] == 20937 )
      {
         printf("pmulhrsw_4 ... ok\n");
      }
      else
      {
         printf("pmulhrsw_4 ... not ok\n");
         printf("  result0.uw[0] = %u (expected %u)\n", result0.uw[0], 60075);
         printf("  result0.uw[1] = %u (expected %u)\n", result0.uw[1], 17037);
         printf("  result0.uw[2] = %u (expected %u)\n", result0.uw[2], 11146);
         printf("  result0.uw[3] = %u (expected %u)\n", result0.uw[3], 25091);
         printf("  result0.uw[4] = %u (expected %u)\n", result0.uw[4], 58695);
         printf("  result0.uw[5] = %u (expected %u)\n", result0.uw[5], 13511);
         printf("  result0.uw[6] = %u (expected %u)\n", result0.uw[6], 8214);
         printf("  result0.uw[7] = %u (expected %u)\n", result0.uw[7], 20937);
      }
   }
   else
   {
      printf("pmulhrsw_4 ... failed\n");
   }

   return;
}

static void pmaddubsw_1(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "pmaddubsw %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 32767 && result0.sw[1] == -32768 && result0.sw[2] == -12730 && result0.sw[3] == 27484 )
      {
         printf("pmaddubsw_1 ... ok\n");
      }
      else
      {
         printf("pmaddubsw_1 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 32767);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -32768);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -12730);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 27484);
      }
   }
   else
   {
      printf("pmaddubsw_1 ... failed\n");
   }

   return;
}

static void pmaddubsw_2(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "pmaddubsw %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 32767 && result0.sw[1] == -32768 && result0.sw[2] == -12730 && result0.sw[3] == 27484 )
      {
         printf("pmaddubsw_2 ... ok\n");
      }
      else
      {
         printf("pmaddubsw_2 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 32767);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -32768);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -12730);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 27484);
      }
   }
   else
   {
      printf("pmaddubsw_2 ... failed\n");
   }

   return;
}

static void pmaddubsw_3(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pmaddubsw %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == 32767 && result0.sw[1] == -32768 && result0.sw[2] == -12730 && result0.sw[3] == 27484 && result0.sw[4] == 32767 && result0.sw[5] == -32768 && result0.sw[6] == -13049 && result0.sw[7] == 27259 )
      {
         printf("pmaddubsw_3 ... ok\n");
      }
      else
      {
         printf("pmaddubsw_3 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 32767);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -32768);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -12730);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 27484);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 32767);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], -32768);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], -13049);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 27259);
      }
   }
   else
   {
      printf("pmaddubsw_3 ... failed\n");
   }

   return;
}

static void pmaddubsw_4(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "pmaddubsw %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == 32767 && result0.sw[1] == -32768 && result0.sw[2] == -12730 && result0.sw[3] == 27484 && result0.sw[4] == 32767 && result0.sw[5] == -32768 && result0.sw[6] == -13049 && result0.sw[7] == 27259 )
      {
         printf("pmaddubsw_4 ... ok\n");
      }
      else
      {
         printf("pmaddubsw_4 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 32767);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -32768);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -12730);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 27484);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 32767);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], -32768);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], -13049);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 27259);
      }
   }
   else
   {
      printf("pmaddubsw_4 ... failed\n");
   }

   return;
}

static void phsubw_1(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "phsubw %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == -512 && result0.sw[1] == -25602 && result0.sw[2] == 27903 && result0.sw[3] == 23478 )
      {
         printf("phsubw_1 ... ok\n");
      }
      else
      {
         printf("phsubw_1 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -512);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -25602);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 27903);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 23478);
      }
   }
   else
   {
      printf("phsubw_1 ... failed\n");
   }

   return;
}

static void phsubw_2(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "phsubw %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == -512 && result0.sw[1] == -25602 && result0.sw[2] == 27903 && result0.sw[3] == 23478 )
      {
         printf("phsubw_2 ... ok\n");
      }
      else
      {
         printf("phsubw_2 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -512);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -25602);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 27903);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 23478);
      }
   }
   else
   {
      printf("phsubw_2 ... failed\n");
   }

   return;
}

static void phsubw_3(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phsubw %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == -512 && result0.sw[1] == -25602 && result0.sw[2] == -3328 && result0.sw[3] == -30672 && result0.sw[4] == 27903 && result0.sw[5] == 23478 && result0.sw[6] == 27391 && result0.sw[7] == 23989 )
      {
         printf("phsubw_3 ... ok\n");
      }
      else
      {
         printf("phsubw_3 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -512);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -25602);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -3328);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], -30672);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 27903);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 23478);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], 27391);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 23989);
      }
   }
   else
   {
      printf("phsubw_3 ... failed\n");
   }

   return;
}

static void phsubw_4(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phsubw %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == -512 && result0.sw[1] == -25602 && result0.sw[2] == -3328 && result0.sw[3] == -30672 && result0.sw[4] == 27903 && result0.sw[5] == 23478 && result0.sw[6] == 27391 && result0.sw[7] == 23989 )
      {
         printf("phsubw_4 ... ok\n");
      }
      else
      {
         printf("phsubw_4 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -512);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -25602);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -3328);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], -30672);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 27903);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 23478);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], 27391);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 23989);
      }
   }
   else
   {
      printf("phsubw_4 ... failed\n");
   }

   return;
}

static void phsubd_1(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "phsubd %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sd[0] == -1698235191L && result0.sd[1] == 1082151370L )
      {
         printf("phsubd_1 ... ok\n");
      }
      else
      {
         printf("phsubd_1 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], -1698235191L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 1082151370L);
      }
   }
   else
   {
      printf("phsubd_1 ... failed\n");
   }

   return;
}

static void phsubd_2(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "phsubd %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sd[0] == -1698235191L && result0.sd[1] == 1082151370L )
      {
         printf("phsubd_2 ... ok\n");
      }
      else
      {
         printf("phsubd_2 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], -1698235191L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 1082151370L);
      }
   }
   else
   {
      printf("phsubd_2 ... failed\n");
   }

   return;
}

static void phsubd_3(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phsubd %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sd[0] == -1698235191L && result0.sd[1] == -1528492107L && result0.sd[2] == 1082151370L && result0.sd[3] == 1115705291L )
      {
         printf("phsubd_3 ... ok\n");
      }
      else
      {
         printf("phsubd_3 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], -1698235191L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], -1528492107L);
         printf("  result0.sd[2] = %ld (expected %ld)\n", result0.sd[2], 1082151370L);
         printf("  result0.sd[3] = %ld (expected %ld)\n", result0.sd[3], 1115705291L);
      }
   }
   else
   {
      printf("phsubd_3 ... failed\n");
   }

   return;
}

static void phsubd_4(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phsubd %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sd[0] == -1698235191L && result0.sd[1] == -1528492107L && result0.sd[2] == 1082151370L && result0.sd[3] == 1115705291L )
      {
         printf("phsubd_4 ... ok\n");
      }
      else
      {
         printf("phsubd_4 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], -1698235191L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], -1528492107L);
         printf("  result0.sd[2] = %ld (expected %ld)\n", result0.sd[2], 1082151370L);
         printf("  result0.sd[3] = %ld (expected %ld)\n", result0.sd[3], 1115705291L);
      }
   }
   else
   {
      printf("phsubd_4 ... failed\n");
   }

   return;
}

static void phsubsw_1(void)
{
   reg64_t arg0 = { .sw = { 20000, -21000, 1245, -1212 } };
   reg64_t arg1 = { .sw = { -17000, 18121, 134, 4552 } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "phsubsw %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == -32768 && result0.sw[1] == -4418 && result0.sw[2] == 32767 && result0.sw[3] == 2457 )
      {
         printf("phsubsw_1 ... ok\n");
      }
      else
      {
         printf("phsubsw_1 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -32768);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -4418);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 32767);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 2457);
      }
   }
   else
   {
      printf("phsubsw_1 ... failed\n");
   }

   return;
}

static void phsubsw_2(void)
{
   reg64_t arg0 = { .sw = { 20000, -21000, 1245, -1212 } };
   reg64_t arg1 = { .sw = { -17000, 18121, 134, 4552 } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "phsubsw %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == -32768 && result0.sw[1] == -4418 && result0.sw[2] == 32767 && result0.sw[3] == 2457 )
      {
         printf("phsubsw_2 ... ok\n");
      }
      else
      {
         printf("phsubsw_2 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -32768);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -4418);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 32767);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 2457);
      }
   }
   else
   {
      printf("phsubsw_2 ... failed\n");
   }

   return;
}

static void phsubsw_3(void)
{
   reg128_t arg0 = { .sw = { 20000, -21000, 1245, -1212, 57, 34, 5788, 234 } };
   reg128_t arg1 = { .sw = { -17000, 18121, 134, 4552, 235, 6356, 123, 75 } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phsubsw %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == -32768 && result0.sw[1] == -4418 && result0.sw[2] == -6121 && result0.sw[3] == 48 && result0.sw[4] == 32767 && result0.sw[5] == 2457 && result0.sw[6] == 23 && result0.sw[7] == 5554 )
      {
         printf("phsubsw_3 ... ok\n");
      }
      else
      {
         printf("phsubsw_3 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -32768);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -4418);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -6121);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 48);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 32767);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 2457);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], 23);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 5554);
      }
   }
   else
   {
      printf("phsubsw_3 ... failed\n");
   }

   return;
}

static void phsubsw_4(void)
{
   reg128_t arg0 = { .sw = { 20000, -21000, 1245, -1212, 57, 34, 5788, 234 } };
   reg128_t arg1 = { .sw = { -17000, 18121, 134, 4552, 235, 6356, 123, 75 } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phsubsw %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == -32768 && result0.sw[1] == -4418 && result0.sw[2] == -6121 && result0.sw[3] == 48 && result0.sw[4] == 32767 && result0.sw[5] == 2457 && result0.sw[6] == 23 && result0.sw[7] == 5554 )
      {
         printf("phsubsw_4 ... ok\n");
      }
      else
      {
         printf("phsubsw_4 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -32768);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -4418);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -6121);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 48);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 32767);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 2457);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], 23);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 5554);
      }
   }
   else
   {
      printf("phsubsw_4 ... failed\n");
   }

   return;
}

static void phaddw_1(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "phaddw %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 12798 && result0.sw[1] == -26002 && result0.sw[2] == -14337 && result0.sw[3] == 13748 )
      {
         printf("phaddw_1 ... ok\n");
      }
      else
      {
         printf("phaddw_1 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 12798);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -26002);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -14337);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 13748);
      }
   }
   else
   {
      printf("phaddw_1 ... failed\n");
   }

   return;
}

static void phaddw_2(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "phaddw %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 12798 && result0.sw[1] == -26002 && result0.sw[2] == -14337 && result0.sw[3] == 13748 )
      {
         printf("phaddw_2 ... ok\n");
      }
      else
      {
         printf("phaddw_2 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 12798);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -26002);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -14337);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 13748);
      }
   }
   else
   {
      printf("phaddw_2 ... failed\n");
   }

   return;
}

static void phaddw_3(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phaddw %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == 12798 && result0.sw[1] == -26002 && result0.sw[2] == 15102 && result0.sw[3] == -31132 && result0.sw[4] == -14337 && result0.sw[5] == 13748 && result0.sw[6] == -14337 && result0.sw[7] == 13747 )
      {
         printf("phaddw_3 ... ok\n");
      }
      else
      {
         printf("phaddw_3 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 12798);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -26002);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 15102);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], -31132);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], -14337);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 13748);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], -14337);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 13747);
      }
   }
   else
   {
      printf("phaddw_3 ... failed\n");
   }

   return;
}

static void phaddw_4(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phaddw %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == 12798 && result0.sw[1] == -26002 && result0.sw[2] == 15102 && result0.sw[3] == -31132 && result0.sw[4] == -14337 && result0.sw[5] == 13748 && result0.sw[6] == -14337 && result0.sw[7] == 13747 )
      {
         printf("phaddw_4 ... ok\n");
      }
      else
      {
         printf("phaddw_4 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 12798);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], -26002);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 15102);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], -31132);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], -14337);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 13748);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], -14337);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 13747);
      }
   }
   else
   {
      printf("phaddw_4 ... failed\n");
   }

   return;
}

static void phaddd_1(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "phaddd %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sd[0] == -1724370123L && result0.sd[1] == 444588852L )
      {
         printf("phaddd_1 ... ok\n");
      }
      else
      {
         printf("phaddd_1 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], -1724370123L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 444588852L);
      }
   }
   else
   {
      printf("phaddd_1 ... failed\n");
   }

   return;
}

static void phaddd_2(void)
{
   reg64_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U } };
   reg64_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "phaddd %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sd[0] == -1724370123L && result0.sd[1] == 444588852L )
      {
         printf("phaddd_2 ... ok\n");
      }
      else
      {
         printf("phaddd_2 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], -1724370123L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], 444588852L);
      }
   }
   else
   {
      printf("phaddd_2 ... failed\n");
   }

   return;
}

static void phaddd_3(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phaddd %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sd[0] == -1724370123L && result0.sd[1] == -1558569399L && result0.sd[2] == 444588852L && result0.sd[3] == 444588851L )
      {
         printf("phaddd_3 ... ok\n");
      }
      else
      {
         printf("phaddd_3 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], -1724370123L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], -1558569399L);
         printf("  result0.sd[2] = %ld (expected %ld)\n", result0.sd[2], 444588852L);
         printf("  result0.sd[3] = %ld (expected %ld)\n", result0.sd[3], 444588851L);
      }
   }
   else
   {
      printf("phaddd_3 ... failed\n");
   }

   return;
}

static void phaddd_4(void)
{
   reg128_t arg0 = { .ub = { 127U, 26U, 128U, 173U, 181U, 200U, 255U, 108U, 127U, 25U, 128U, 174U, 180U, 201U, 255U, 107U } };
   reg128_t arg1 = { .ub = { 255U, 151U, 255U, 153U, 54U, 155U, 56U, 255U, 255U, 150U, 255U, 163U, 74U, 135U, 26U, 255U } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phaddd %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sd[0] == -1724370123L && result0.sd[1] == -1558569399L && result0.sd[2] == 444588852L && result0.sd[3] == 444588851L )
      {
         printf("phaddd_4 ... ok\n");
      }
      else
      {
         printf("phaddd_4 ... not ok\n");
         printf("  result0.sd[0] = %ld (expected %ld)\n", result0.sd[0], -1724370123L);
         printf("  result0.sd[1] = %ld (expected %ld)\n", result0.sd[1], -1558569399L);
         printf("  result0.sd[2] = %ld (expected %ld)\n", result0.sd[2], 444588852L);
         printf("  result0.sd[3] = %ld (expected %ld)\n", result0.sd[3], 444588851L);
      }
   }
   else
   {
      printf("phaddd_4 ... failed\n");
   }

   return;
}

static void phaddsw_1(void)
{
   reg64_t arg0 = { .sw = { 20000, -21000, 1245, -1212 } };
   reg64_t arg1 = { .sw = { -17000, 18121, 134, 4552 } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %0, %%mm6\n"
         "movq %1, %%mm7\n"
         "phaddsw %%mm6, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 1121 && result0.sw[1] == 4686 && result0.sw[2] == -1000 && result0.sw[3] == 33 )
      {
         printf("phaddsw_1 ... ok\n");
      }
      else
      {
         printf("phaddsw_1 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 1121);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 4686);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -1000);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 33);
      }
   }
   else
   {
      printf("phaddsw_1 ... failed\n");
   }

   return;
}

static void phaddsw_2(void)
{
   reg64_t arg0 = { .sw = { 20000, -21000, 1245, -1212 } };
   reg64_t arg1 = { .sw = { -17000, 18121, 134, 4552 } };
   reg64_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movq %1, %%mm7\n"
         "phaddsw %0, %%mm7\n"
         "movq %%mm7, %2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "mm6", "mm7"
      );

      if (result0.sw[0] == 1121 && result0.sw[1] == 4686 && result0.sw[2] == -1000 && result0.sw[3] == 33 )
      {
         printf("phaddsw_2 ... ok\n");
      }
      else
      {
         printf("phaddsw_2 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], 1121);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 4686);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], -1000);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 33);
      }
   }
   else
   {
      printf("phaddsw_2 ... failed\n");
   }

   return;
}

static void phaddsw_3(void)
{
   reg128_t arg0 = { .sw = { 20000, 21000, 1245, -1212, 57, 34, 5788, 234 } };
   reg128_t arg1 = { .sw = { -17000, -18121, 134, 4552, 235, 6356, 123, 75 } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%0, %%xmm4\n"
         "movhps 8%0, %%xmm4\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phaddsw %%xmm4, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == -32768 && result0.sw[1] == 4686 && result0.sw[2] == 6591 && result0.sw[3] == 198 && result0.sw[4] == 32767 && result0.sw[5] == 33 && result0.sw[6] == 91 && result0.sw[7] == 6022 )
      {
         printf("phaddsw_3 ... ok\n");
      }
      else
      {
         printf("phaddsw_3 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -32768);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 4686);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 6591);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 198);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 32767);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 33);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], 91);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 6022);
      }
   }
   else
   {
      printf("phaddsw_3 ... failed\n");
   }

   return;
}

static void phaddsw_4(void)
{
   reg128_t arg0 = { .sw = { 20000, 21000, 1245, -1212, 57, 34, 5788, 234 } };
   reg128_t arg1 = { .sw = { -17000, -18121, 134, 4552, 235, 6356, 123, 75 } };
   reg128_t result0;
   char state[108];

   if (sigsetjmp(catchpoint, 1) == 0)
   {
      asm(
         "fsave %3\n"
         "movlps 0%1, %%xmm5\n"
         "movhps 8%1, %%xmm5\n"
         "phaddsw %0, %%xmm5\n"
         "movlps %%xmm5, 0%2\n"
         "movhps %%xmm5, 8%2\n"
         "frstor %3\n"
         :
         : "m" (arg0), "m" (arg1), "m" (result0), "m" (state[0])
         : "xmm4", "xmm5"
      );

      if (result0.sw[0] == -32768 && result0.sw[1] == 4686 && result0.sw[2] == 6591 && result0.sw[3] == 198 && result0.sw[4] == 32767 && result0.sw[5] == 33 && result0.sw[6] == 91 && result0.sw[7] == 6022 )
      {
         printf("phaddsw_4 ... ok\n");
      }
      else
      {
         printf("phaddsw_4 ... not ok\n");
         printf("  result0.sw[0] = %d (expected %d)\n", result0.sw[0], -32768);
         printf("  result0.sw[1] = %d (expected %d)\n", result0.sw[1], 4686);
         printf("  result0.sw[2] = %d (expected %d)\n", result0.sw[2], 6591);
         printf("  result0.sw[3] = %d (expected %d)\n", result0.sw[3], 198);
         printf("  result0.sw[4] = %d (expected %d)\n", result0.sw[4], 32767);
         printf("  result0.sw[5] = %d (expected %d)\n", result0.sw[5], 33);
         printf("  result0.sw[6] = %d (expected %d)\n", result0.sw[6], 91);
         printf("  result0.sw[7] = %d (expected %d)\n", result0.sw[7], 6022);
      }
   }
   else
   {
      printf("phaddsw_4 ... failed\n");
   }

   return;
}

int main(int argc, char **argv)
{
   signal(SIGILL, handle_sigill);

   psignb_1();
   psignb_2();
   psignb_3();
   psignb_4();
   psignw_1();
   psignw_2();
   psignw_3();
   psignw_4();
   psignd_1();
   psignd_2();
   psignd_3();
   psignd_4();
   pabsb_1();
   pabsb_2();
   pabsb_3();
   pabsb_4();
   pabsw_1();
   pabsw_2();
   pabsw_3();
   pabsw_4();
   pabsd_1();
   pabsd_2();
   pabsd_3();
   pabsd_4();
   palignr_1();
   palignr_2();
   palignr_3();
   palignr_4();
   palignr_5();
   palignr_6();
   palignr_7();
   palignr_8();
   palignr_9();
   palignr_10();
   palignr_11();
   palignr_12();
   palignr_13();
   palignr_14();
   palignr_15();
   palignr_16();
   palignr_17();
   palignr_18();
   palignr_19();
   palignr_20();
   palignr_21();
   palignr_22();
   palignr_23();
   palignr_24();
   palignr_25();
   palignr_26();
   palignr_27();
   palignr_28();
   palignr_29();
   palignr_30();
   palignr_31();
   palignr_32();
   palignr_33();
   palignr_34();
   palignr_35();
   palignr_36();
   palignr_37();
   palignr_38();
   palignr_39();
   palignr_40();
   palignr_41();
   palignr_42();
   palignr_43();
   palignr_44();
   palignr_45();
   palignr_46();
   palignr_47();
   palignr_48();
   palignr_49();
   palignr_50();
   palignr_51();
   palignr_52();
   palignr_53();
   palignr_54();
   palignr_55();
   palignr_56();
   palignr_57();
   palignr_58();
   palignr_59();
   palignr_60();
   palignr_61();
   palignr_62();
   palignr_63();
   palignr_64();
   palignr_65();
   palignr_66();
   palignr_67();
   palignr_68();
   palignr_69();
   palignr_70();
   palignr_71();
   palignr_72();
   palignr_73();
   palignr_74();
   palignr_75();
   palignr_76();
   palignr_77();
   palignr_78();
   palignr_79();
   palignr_80();
   palignr_81();
   palignr_82();
   palignr_83();
   palignr_84();
   palignr_85();
   palignr_86();
   palignr_87();
   palignr_88();
   palignr_89();
   palignr_90();
   palignr_91();
   palignr_92();
   palignr_93();
   palignr_94();
   palignr_95();
   palignr_96();
   palignr_97();
   palignr_98();
   palignr_99();
   palignr_100();
   palignr_101();
   palignr_102();
   palignr_103();
   palignr_104();
   palignr_105();
   palignr_106();
   palignr_107();
   palignr_108();
   palignr_109();
   palignr_110();
   palignr_111();
   palignr_112();
   palignr_113();
   palignr_114();
   palignr_115();
   palignr_116();
   palignr_117();
   palignr_118();
   palignr_119();
   palignr_120();
   palignr_121();
   palignr_122();
   palignr_123();
   palignr_124();
   palignr_125();
   palignr_126();
   palignr_127();
   palignr_128();
   pshufb_1();
   pshufb_2();
   pshufb_3();
   pshufb_4();
   pmulhrsw_1();
   pmulhrsw_2();
   pmulhrsw_3();
   pmulhrsw_4();
   pmaddubsw_1();
   pmaddubsw_2();
   pmaddubsw_3();
   pmaddubsw_4();
   phsubw_1();
   phsubw_2();
   phsubw_3();
   phsubw_4();
   phsubd_1();
   phsubd_2();
   phsubd_3();
   phsubd_4();
   phsubsw_1();
   phsubsw_2();
   phsubsw_3();
   phsubsw_4();
   phaddw_1();
   phaddw_2();
   phaddw_3();
   phaddw_4();
   phaddd_1();
   phaddd_2();
   phaddd_3();
   phaddd_4();
   phaddsw_1();
   phaddsw_2();
   phaddsw_3();
   phaddsw_4();

   exit(0);
}

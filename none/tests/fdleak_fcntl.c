#include <unistd.h>
#include <stdio.h>
#include <fcntl.h>
#include "fdleak.h"
int
main (int argc, char **argv)
{
   int s1;






   CLOSE_INHERITED_FDS;

   s1 = open("/dev/null", O_RDONLY);
   if(fcntl(s1, F_DUPFD, s1) == -1) perror("fcntl");
   return 0;
}

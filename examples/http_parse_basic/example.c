#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define MALLOC_SIZE 4
// times out with 64 bit buffer

// cntlm 22

char *buf;
char password = 7; // secret value; has to be a variable so that we get a Gamma_password variable
char stext[11] = "helloo";



int main() {
    char *pos = NULL, *dom = NULL;
    

   //memset(stext, 'h', 10);
   stext[5] = password;
   buf = malloc(11);
   // it only verifies if memcpy is the WHOLE string
   memcpy(buf, stext, strlen(stext)); // inlined by -O2

   puts(buf);

   // find the split between username and password ("username:password")
   pos = buf + 2;
    
  // including this makes verification fail
  *pos = 0;

  memset(buf, 1, strlen(buf));
  free(buf); // requires secret[i] == true
}


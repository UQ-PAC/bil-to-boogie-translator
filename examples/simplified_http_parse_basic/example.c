#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define MALLOC_SIZE 10


// cntlm 22

char *buf;
char password = 7; // secret value; has to be a variable so that we get a Gamma_password variable
char stext[11] = "sometext";



int main() {
    char *pos = NULL, *dom = NULL;
    

   stext[5] = password;
   buf = malloc(strlen(stext) + 1);
   memcpy(buf, stext, strlen(stext) + 1); // inlined by -O2

   puts(buf);

   // find the split between username and password ("username:password")
   pos = buf + 2;

  *pos = 0;

  memset(buf, 0, strlen(buf));
  free(buf); // requires secret[i] == true

}


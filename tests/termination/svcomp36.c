/*
 * Name:           name
 * Linear-program: true
 * Linear-rank:    true
 * Conditional:    false
 * Float:          false
 * Bitvector:      false
 * Lexicographic:  1
 */
/*
 * Date: 17.12.2013
 * Author: Thomas Ströder
 */
#include <stdlib.h>

extern int nondet(void);

/* Returns some null-terminated string. */
char *__VERIFIER_nondet_String(void)
{
  int length;
  if (length < 1) {
    length = 1;
  }
  char *nondetString = (char *) malloc(length * sizeof(char));
  nondetString[length - 1] = '\0';
  return nondetString;
}





char *(cstrchr) (const char *s, int c) {
  /* Scan s for the character.  When this loop is finished,
     s will either point to the end of the string or the
     character we were looking for.  */
  while (*s != '\0' && *s != (char) c)
    s++;
  return ((*s == c) ? (char *) s : 0);
}

int main()
{
  cstrchr(__VERIFIER_nondet_String(), nondet());
  return 0;
}

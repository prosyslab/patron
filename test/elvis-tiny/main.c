extern char *getenv(const char* env);
extern int *sprintf(char *buffer, const char *format_string, const char *arg);
extern int *snprintf(char *buffer, unsigned int n, const char *format_string, const char *arg);
extern int *printf(const char *format_string, const char *arg);

typedef union {
  char c[1024];
  unsigned short n[1024 / sizeof(unsigned short)];
} BLK;

BLK tmpblk;

int main(int argc, char *argv[]) {
  char *str;
  str = getenv("HOME"); // src

  if (str) {
   sprintf(tmpblk.c, "%s%c%s", str, '/', "elvis.rc"); // BO // snk
  }

  return 0;
}


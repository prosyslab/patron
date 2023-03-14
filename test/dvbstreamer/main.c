extern char *getenv(const char* env);
extern int *sprintf(char *buffer, const char *format_string, const char *arg);
extern int *snprintf(char *buffer, unsigned int n, const char *format_string, const char *arg);
extern int *printf(const char *format_string, const char *arg);

char DataDirectory[100];

int main(int argc, char *argv[]) {
  sprintf(DataDirectory, "%s/.dvbstreamer", getenv("HOME")); // BO // src // snk
  snprintf(DataDirectory, sizeof(DataDirectory), "%s/.dvbstreamer", getenv("HOME")); 
/* Expected Patch */
  return 0;
}

int main(void) {
  char *ptr_h;
  char h[64];

  ptr_h = getenv("HOME"); // src
  if (ptr_h != (void *) 0) {
    sprintf(h, "Your home directory is: %s !", ptr_h); // BO // snk
    printf("%s\n", h);
  }

  return 0;
}


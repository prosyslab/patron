extern int* fopen(char* filename, const char* mode);
extern int fread(unsigned char* buffer, int size, int count, int* fd);
extern int strncmp(const char* str1, const char* str2, int n);
extern void *malloc(unsigned int size);

long ToL(unsigned char *puffer) {
    return (puffer[0] | puffer[1] << 8 | puffer[2] << 16 | puffer[3] << 24);
}
short ToS(unsigned char *puffer) { return (puffer[0] | puffer[1] << 8); }


int bmp_load_image(char *filename) {
    int* fd = fopen(filename, "rb"); // src
    unsigned char* buffer;
    if (fread(buffer, 18, 1, fd) || (strncmp((const char *)buffer, "BM", 2)))
        return -1;
    long biWidth = ToL(&buffer[0x00]); // n1
    short biBitCnt = ToS(&buffer[0x0A]); // n2
    int rowbytes = ((biWidth * biBitCnt - 1) / 32) * 4 + 4; // IO // snk
    void* bitmap = malloc(rowbytes);
    return 0;
}

int main(int argc, char* argv[]) {
    bmp_load_image(argv[1]);
}

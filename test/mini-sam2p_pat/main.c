long ToL(unsigned char *puffer) {
    return (puffer[0] | puffer[1] << 8 | puffer[2] << 16 | puffer[3] << 24);
}
short ToS(unsigned char *puffer) { return (puffer[0] | puffer[1] << 8); }

int main() {
    char * filename = input();
    int fd = fopen(filename, "rb"); // src
    unsigned char buffer[64];
    fread(buffer, 18, 1, fd);
    long biWidth = ToL(buffer); // n1
    short biBitCnt = ToS(buffer + 0x0A); // n2
    if (biWidth * biBitCnt < biWidth)
        return -1; // Given Patch // P
    int rowbytes = ((biWidth * biBitCnt - 1) / 32) * 4 + 4; // IO // snk
    void* bitmap = malloc(rowbytes);
    return 0;
}

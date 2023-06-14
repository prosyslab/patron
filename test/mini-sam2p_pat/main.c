int main()
{
    char *filename = input();
    unsigned char buffer[64];
    int fd = fopen(filename, "rb"); // src
    fread(buffer, 18, 1, fd);
    unnecessary(buffer, 4, fd);                                                    // L3
    long biWidth = buffer[0] | buffer[1] << 8 | buffer[2] << 16 | buffer[3] << 24; // n1
    short biBitCnt = buffer[10] | buffer[11] << 8;                                 // n2
    if ((long)biWidth * biBitCnt > 2147483647)
        return -1;                                          // Given Patch // P
    int rowbytes = ((biWidth * biBitCnt - 1) / 32) * 4 + 4; // IO // snk
    void *bitmap = malloc(rowbytes);
    return 0;
}

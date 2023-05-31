int main()
{
    char *filename = input();                                                      // L0
    unsigned char buffer[64];                                                      // L1
    int *fd = fopen(filename, "rb");                                               // L2
    fread(buffer, 18, 1, fd);                                                      // src
    unnecessary(buffer, 4, fd);                                                    // L3
    long biWidth = buffer[0] | buffer[1] << 8 | buffer[2] << 16 | buffer[3] << 24; // n1
    short biBitCnt = buffer[10] | buffer[11] << 8;                                 // n2
    int rowbytes = ((biWidth * biBitCnt - 1) / 32) * 4 + 4;                        // snk
    void *bitmap = malloc(rowbytes);
    return 0;
}
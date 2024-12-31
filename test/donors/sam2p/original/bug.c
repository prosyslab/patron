int main()
{
    char *filename = input();
    unsigned char buffer[64];
    int fd = fopen(filename, "rb"); // src
    fread(buffer, 18, 1, fd);
    unnecessary(buffer, 4, fd);                                                    // L3
    long biWidth = buffer[0] | buffer[1] << 8 | buffer[2] << 16 | buffer[3] << 24; // n1
    short biBitCnt = buffer[10] | buffer[11] << 8;                                 // n2
    int rowbytes = biWidth * biBitCnt;                        // IO // snk
    void *bitmap = malloc(rowbytes);
    return 0;
}
int main()
{
    char *filename = input();
    unsigned char buffer[64];
    int fd = fopen(filename, "rb"); // src
    
    fread(buffer, 18, 1, fd);
    unnecessary(buffer, 4, fd);

    long biWidth = buffer[0] | buffer[1] << 8 | buffer[2] << 16 | buffer[3] << 24;
    short biBitCnt = buffer[10] | buffer[11] << 8;                                
    int rowbytes = biWidth * biBitCnt;                        // IO snk
    void *bitmap = malloc(rowbytes);
    return 0;
}
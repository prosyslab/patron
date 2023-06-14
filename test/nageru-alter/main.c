extern int *fopen(char *filename, const char *mode);
extern int fread(unsigned char *buffer, int size, int count, int *fd);
extern int strncmp(const char *str1, const char *str2, int n);
extern void *malloc(unsigned int size);

int read_flow(const char *filename)
{
    int *flowfp = fopen(filename, "rb");
    unsigned int hdr, width, height;
    fread(&hdr, 18, 1, flowfp); // src
                                // fread(&width, sizeof(width), 1, flowfp);
                                // fread(&height, sizeof(height), 1, flowfp);
    width = hdr + 0;            // n1
    height = hdr + 0;           // n2

    /* if (width * height < width) // Expected Patch // P */
    /*     return -1; */

    int flow_size = width * height;
    void *flow = malloc(flow_size); // IO // snk

    // fread(&hdr, width * height, 1, flowfp);

    return 0;
}

int main(int argc, char *argv[])
{
    read_flow(argv[1]);
}

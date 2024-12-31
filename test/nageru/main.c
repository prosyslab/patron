int main(int argc, char* argv[]) {
    char * filename = input();
    int *flowfp = fopen(filename, "rb");
    unsigned int hdr, width, height;
    fread(&hdr, sizeof(hdr), 1, flowfp);
	fread(&width, sizeof(width), 1, flowfp); // n1
	fread(&height, sizeof(height), 1, flowfp); // n2

    /* if (width * height < width) // Expected Patch // P */
    /*     return -1; */

    void* flow = malloc(width * height); // IO // snk

	// fread(&hdr, width * height, 1, flowfp);

    return 0;
}

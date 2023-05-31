int main()
{
    char a = getchar();
    char b = getchar();
    char x, y;

    x = a;
    y = b;

    if ((int)x * y > 127)
        return 1;

    char c = x * y;

    return 0;
}
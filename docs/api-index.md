# The Quarz standard library

The API of the standard library of [Quarz](https://quarz.dev/): the built-in classes (`Int`, `String`, `Array`, `Hash`, `Task`, `Channel`), and the modules a program requires (`JSON`, `HTTP`, `Socket`, `Crypto`, `Test`). The pages below come from the comments in the library's source ([docs/13](https://github.com/quarz-lang/quarz/blob/main/docs/13-doc-comments.md)).

## Cogs

The quarz-lang cogs publish their APIs the same way ([docs/10 §8](https://github.com/quarz-lang/quarz/blob/main/docs/10-cogs.md#8-publishing-the-api)):

- [pg](https://pg.api.quarz.dev/): a PostgreSQL client.
- [rotor](https://rotor.api.quarz.dev/): models, queries and migrations on PostgreSQL.
- [aws](https://aws.api.quarz.dev/): AWS credentials, request signing and services.
- [divider](https://divider.api.quarz.dev/): a job queue on PostgreSQL.
- [bezel](https://bezel.api.quarz.dev/): a web framework.
